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
% DateTime   : Thu Dec  3 09:50:33 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   65 (  68 expanded)
%              Number of leaves         :   34 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 (  78 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_103,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_64,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),B_39)
      | r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_143,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_127,plain,(
    ! [E_52,A_53,B_54] : r2_hidden(E_52,k1_enumset1(A_53,B_54,E_52)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_53,B_54,E_52] : ~ v1_xboole_0(k1_enumset1(A_53,B_54,E_52)) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_163,plain,(
    ! [A_66,B_67] : ~ v1_xboole_0(k2_tarski(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_131])).

tff(c_169,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_163])).

tff(c_24,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_170,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_263,plain,(
    ! [B_83,A_84] : k3_tarski(k2_tarski(B_83,A_84)) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_170])).

tff(c_62,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_269,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,A_84) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_62])).

tff(c_66,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_289,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_66])).

tff(c_350,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(B_89,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_354,plain,
    ( k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_289,c_350])).

tff(c_364,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_354])).

tff(c_418,plain,(
    ! [A_99,C_100,B_101] :
      ( r1_xboole_0(A_99,C_100)
      | ~ r1_xboole_0(A_99,k2_xboole_0(B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_436,plain,(
    ! [A_102] :
      ( r1_xboole_0(A_102,k1_tarski('#skF_5'))
      | ~ r1_xboole_0(A_102,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_418])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_371,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,k3_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_406,plain,(
    ! [A_96,B_97] :
      ( ~ r1_xboole_0(A_96,B_97)
      | v1_xboole_0(k3_xboole_0(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_4,c_371])).

tff(c_409,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_406])).

tff(c_440,plain,
    ( v1_xboole_0(k1_tarski('#skF_5'))
    | ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_436,c_409])).

tff(c_446,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_440])).

tff(c_459,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_446])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:15:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.37  
% 2.44/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3
% 2.44/1.37  
% 2.44/1.37  %Foreground sorts:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Background operators:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Foreground operators:
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.44/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.44/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.44/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.44/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.37  
% 2.44/1.38  tff(f_108, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.44/1.38  tff(f_101, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.44/1.38  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.44/1.38  tff(f_92, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.44/1.38  tff(f_88, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.44/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.44/1.38  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.44/1.38  tff(f_73, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.44/1.38  tff(f_103, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.44/1.38  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.44/1.38  tff(f_69, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.44/1.38  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.44/1.38  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.44/1.38  tff(c_64, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.44/1.38  tff(c_60, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), B_39) | r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.44/1.38  tff(c_52, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.44/1.38  tff(c_143, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.44/1.38  tff(c_127, plain, (![E_52, A_53, B_54]: (r2_hidden(E_52, k1_enumset1(A_53, B_54, E_52)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.44/1.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.38  tff(c_131, plain, (![A_53, B_54, E_52]: (~v1_xboole_0(k1_enumset1(A_53, B_54, E_52)))), inference(resolution, [status(thm)], [c_127, c_2])).
% 2.44/1.38  tff(c_163, plain, (![A_66, B_67]: (~v1_xboole_0(k2_tarski(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_131])).
% 2.44/1.38  tff(c_169, plain, (![A_28]: (~v1_xboole_0(k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_163])).
% 2.44/1.38  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.38  tff(c_26, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.38  tff(c_170, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.38  tff(c_263, plain, (![B_83, A_84]: (k3_tarski(k2_tarski(B_83, A_84))=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_26, c_170])).
% 2.44/1.38  tff(c_62, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.44/1.38  tff(c_269, plain, (![B_83, A_84]: (k2_xboole_0(B_83, A_84)=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_263, c_62])).
% 2.44/1.38  tff(c_66, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.44/1.38  tff(c_289, plain, (r1_tarski(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_66])).
% 2.44/1.38  tff(c_350, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(B_89, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.44/1.38  tff(c_354, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_289, c_350])).
% 2.44/1.38  tff(c_364, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_354])).
% 2.44/1.38  tff(c_418, plain, (![A_99, C_100, B_101]: (r1_xboole_0(A_99, C_100) | ~r1_xboole_0(A_99, k2_xboole_0(B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.44/1.38  tff(c_436, plain, (![A_102]: (r1_xboole_0(A_102, k1_tarski('#skF_5')) | ~r1_xboole_0(A_102, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_364, c_418])).
% 2.44/1.38  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.44/1.38  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.38  tff(c_371, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, k3_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.44/1.38  tff(c_406, plain, (![A_96, B_97]: (~r1_xboole_0(A_96, B_97) | v1_xboole_0(k3_xboole_0(A_96, B_97)))), inference(resolution, [status(thm)], [c_4, c_371])).
% 2.44/1.38  tff(c_409, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | v1_xboole_0(A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_406])).
% 2.44/1.38  tff(c_440, plain, (v1_xboole_0(k1_tarski('#skF_5')) | ~r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_436, c_409])).
% 2.44/1.38  tff(c_446, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_169, c_440])).
% 2.44/1.38  tff(c_459, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_446])).
% 2.44/1.38  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_459])).
% 2.44/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.38  
% 2.44/1.38  Inference rules
% 2.44/1.38  ----------------------
% 2.44/1.38  #Ref     : 0
% 2.44/1.38  #Sup     : 95
% 2.44/1.38  #Fact    : 0
% 2.44/1.38  #Define  : 0
% 2.44/1.38  #Split   : 1
% 2.44/1.38  #Chain   : 0
% 2.44/1.38  #Close   : 0
% 2.44/1.38  
% 2.44/1.38  Ordering : KBO
% 2.44/1.38  
% 2.44/1.38  Simplification rules
% 2.44/1.38  ----------------------
% 2.44/1.38  #Subsume      : 11
% 2.44/1.38  #Demod        : 23
% 2.44/1.38  #Tautology    : 56
% 2.44/1.38  #SimpNegUnit  : 3
% 2.44/1.38  #BackRed      : 2
% 2.44/1.38  
% 2.44/1.38  #Partial instantiations: 0
% 2.44/1.38  #Strategies tried      : 1
% 2.44/1.38  
% 2.44/1.38  Timing (in seconds)
% 2.44/1.38  ----------------------
% 2.44/1.39  Preprocessing        : 0.33
% 2.44/1.39  Parsing              : 0.18
% 2.44/1.39  CNF conversion       : 0.02
% 2.44/1.39  Main loop            : 0.23
% 2.44/1.39  Inferencing          : 0.08
% 2.44/1.39  Reduction            : 0.08
% 2.44/1.39  Demodulation         : 0.06
% 2.44/1.39  BG Simplification    : 0.02
% 2.44/1.39  Subsumption          : 0.04
% 2.44/1.39  Abstraction          : 0.01
% 2.44/1.39  MUC search           : 0.00
% 2.44/1.39  Cooper               : 0.00
% 2.44/1.39  Total                : 0.60
% 2.44/1.39  Index Insertion      : 0.00
% 2.44/1.39  Index Deletion       : 0.00
% 2.44/1.39  Index Matching       : 0.00
% 2.44/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
