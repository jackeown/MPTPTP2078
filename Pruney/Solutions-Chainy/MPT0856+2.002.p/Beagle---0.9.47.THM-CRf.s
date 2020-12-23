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
% DateTime   : Thu Dec  3 10:08:52 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   62 (  82 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 110 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(k1_zfmisc_1(C),B) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70,plain,(
    ! [A_51,B_50] : r1_tarski(A_51,k2_xboole_0(B_50,A_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_26,plain,(
    ! [A_20] : r2_hidden(A_20,'#skF_2'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_155,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_174,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(A_80,B_81)
      | ~ r1_tarski('#skF_2'(A_80),B_81) ) ),
    inference(resolution,[status(thm)],[c_26,c_155])).

tff(c_191,plain,(
    ! [A_82,B_83] : r2_hidden(A_82,k2_xboole_0(B_83,'#skF_2'(A_82))) ),
    inference(resolution,[status(thm)],[c_70,c_174])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_329,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden(A_100,B_101)
      | ~ r1_tarski(k2_xboole_0(B_102,'#skF_2'(A_100)),B_101) ) ),
    inference(resolution,[status(thm)],[c_191,c_4])).

tff(c_375,plain,(
    ! [A_108,B_109,B_110] : r2_hidden(A_108,k2_xboole_0(B_109,k2_xboole_0(B_110,'#skF_2'(A_108)))) ),
    inference(resolution,[status(thm)],[c_70,c_329])).

tff(c_389,plain,(
    ! [A_108,B_109,B_2] : r2_hidden(A_108,k2_xboole_0(B_109,k2_xboole_0('#skF_2'(A_108),B_2))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_375])).

tff(c_40,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5')
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_114,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_478,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden(A_126,k4_xboole_0(B_127,k1_tarski(C_128)))
      | C_128 = A_126
      | ~ r2_hidden(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [B_39,A_38] :
      ( k2_xboole_0(k4_xboole_0(B_39,k1_tarski(A_38)),k1_tarski(A_38)) = B_39
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_421,plain,(
    ! [A_114,B_115] :
      ( k2_xboole_0(k1_tarski(A_114),k4_xboole_0(B_115,k1_tarski(A_114))) = B_115
      | ~ r2_hidden(A_114,B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_436,plain,(
    ! [A_116,B_117] :
      ( r1_tarski(k1_tarski(A_116),B_117)
      | ~ r2_hidden(A_116,B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_10])).

tff(c_42,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_131,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden(k1_mcart_1(A_66),B_67)
      | ~ r2_hidden(A_66,k2_zfmisc_1(B_67,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_138,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_131])).

tff(c_269,plain,(
    ! [B_92] :
      ( r2_hidden(k1_mcart_1('#skF_3'),B_92)
      | ~ r1_tarski(k1_tarski('#skF_4'),B_92) ) ),
    inference(resolution,[status(thm)],[c_138,c_155])).

tff(c_32,plain,(
    ! [C_42,B_41] : ~ r2_hidden(C_42,k4_xboole_0(B_41,k1_tarski(C_42))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_290,plain,(
    ! [B_41] : ~ r1_tarski(k1_tarski('#skF_4'),k4_xboole_0(B_41,k1_tarski(k1_mcart_1('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_269,c_32])).

tff(c_442,plain,(
    ! [B_41] : ~ r2_hidden('#skF_4',k4_xboole_0(B_41,k1_tarski(k1_mcart_1('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_436,c_290])).

tff(c_482,plain,(
    ! [B_127] :
      ( k1_mcart_1('#skF_3') = '#skF_4'
      | ~ r2_hidden('#skF_4',B_127) ) ),
    inference(resolution,[status(thm)],[c_478,c_442])).

tff(c_504,plain,(
    ! [B_129] : ~ r2_hidden('#skF_4',B_129) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_482])).

tff(c_532,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_389,c_504])).

tff(c_533,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_556,plain,(
    ! [A_138,C_139,B_140] :
      ( r2_hidden(k2_mcart_1(A_138),C_139)
      | ~ r2_hidden(A_138,k2_zfmisc_1(B_140,C_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_561,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_556])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.41  %$ r2_tarski > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.67/1.41  
% 2.67/1.41  %Foreground sorts:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Background operators:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Foreground operators:
% 2.67/1.41  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 2.67/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.67/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.67/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.41  
% 2.67/1.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.67/1.42  tff(f_36, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.67/1.42  tff(f_69, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: (r2_hidden(C, B) => r2_hidden(k1_zfmisc_1(C), B)))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 2.67/1.42  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.67/1.42  tff(f_93, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.67/1.42  tff(f_80, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.67/1.42  tff(f_73, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.67/1.42  tff(f_86, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.67/1.42  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.42  tff(c_55, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.42  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.67/1.42  tff(c_70, plain, (![A_51, B_50]: (r1_tarski(A_51, k2_xboole_0(B_50, A_51)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_10])).
% 2.67/1.42  tff(c_26, plain, (![A_20]: (r2_hidden(A_20, '#skF_2'(A_20)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.67/1.42  tff(c_155, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.67/1.42  tff(c_174, plain, (![A_80, B_81]: (r2_hidden(A_80, B_81) | ~r1_tarski('#skF_2'(A_80), B_81))), inference(resolution, [status(thm)], [c_26, c_155])).
% 2.67/1.42  tff(c_191, plain, (![A_82, B_83]: (r2_hidden(A_82, k2_xboole_0(B_83, '#skF_2'(A_82))))), inference(resolution, [status(thm)], [c_70, c_174])).
% 2.67/1.42  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.67/1.42  tff(c_329, plain, (![A_100, B_101, B_102]: (r2_hidden(A_100, B_101) | ~r1_tarski(k2_xboole_0(B_102, '#skF_2'(A_100)), B_101))), inference(resolution, [status(thm)], [c_191, c_4])).
% 2.67/1.42  tff(c_375, plain, (![A_108, B_109, B_110]: (r2_hidden(A_108, k2_xboole_0(B_109, k2_xboole_0(B_110, '#skF_2'(A_108)))))), inference(resolution, [status(thm)], [c_70, c_329])).
% 2.67/1.42  tff(c_389, plain, (![A_108, B_109, B_2]: (r2_hidden(A_108, k2_xboole_0(B_109, k2_xboole_0('#skF_2'(A_108), B_2))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_375])).
% 2.67/1.42  tff(c_40, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5') | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.42  tff(c_114, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_40])).
% 2.67/1.42  tff(c_478, plain, (![A_126, B_127, C_128]: (r2_hidden(A_126, k4_xboole_0(B_127, k1_tarski(C_128))) | C_128=A_126 | ~r2_hidden(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.67/1.42  tff(c_28, plain, (![B_39, A_38]: (k2_xboole_0(k4_xboole_0(B_39, k1_tarski(A_38)), k1_tarski(A_38))=B_39 | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.42  tff(c_421, plain, (![A_114, B_115]: (k2_xboole_0(k1_tarski(A_114), k4_xboole_0(B_115, k1_tarski(A_114)))=B_115 | ~r2_hidden(A_114, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 2.67/1.42  tff(c_436, plain, (![A_116, B_117]: (r1_tarski(k1_tarski(A_116), B_117) | ~r2_hidden(A_116, B_117))), inference(superposition, [status(thm), theory('equality')], [c_421, c_10])).
% 2.67/1.42  tff(c_42, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.42  tff(c_131, plain, (![A_66, B_67, C_68]: (r2_hidden(k1_mcart_1(A_66), B_67) | ~r2_hidden(A_66, k2_zfmisc_1(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.67/1.42  tff(c_138, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_131])).
% 2.67/1.42  tff(c_269, plain, (![B_92]: (r2_hidden(k1_mcart_1('#skF_3'), B_92) | ~r1_tarski(k1_tarski('#skF_4'), B_92))), inference(resolution, [status(thm)], [c_138, c_155])).
% 2.67/1.42  tff(c_32, plain, (![C_42, B_41]: (~r2_hidden(C_42, k4_xboole_0(B_41, k1_tarski(C_42))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.67/1.42  tff(c_290, plain, (![B_41]: (~r1_tarski(k1_tarski('#skF_4'), k4_xboole_0(B_41, k1_tarski(k1_mcart_1('#skF_3')))))), inference(resolution, [status(thm)], [c_269, c_32])).
% 2.67/1.42  tff(c_442, plain, (![B_41]: (~r2_hidden('#skF_4', k4_xboole_0(B_41, k1_tarski(k1_mcart_1('#skF_3')))))), inference(resolution, [status(thm)], [c_436, c_290])).
% 2.67/1.42  tff(c_482, plain, (![B_127]: (k1_mcart_1('#skF_3')='#skF_4' | ~r2_hidden('#skF_4', B_127))), inference(resolution, [status(thm)], [c_478, c_442])).
% 2.67/1.42  tff(c_504, plain, (![B_129]: (~r2_hidden('#skF_4', B_129))), inference(negUnitSimplification, [status(thm)], [c_114, c_482])).
% 2.67/1.42  tff(c_532, plain, $false, inference(resolution, [status(thm)], [c_389, c_504])).
% 2.67/1.42  tff(c_533, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 2.67/1.42  tff(c_556, plain, (![A_138, C_139, B_140]: (r2_hidden(k2_mcart_1(A_138), C_139) | ~r2_hidden(A_138, k2_zfmisc_1(B_140, C_139)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.67/1.42  tff(c_561, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_42, c_556])).
% 2.67/1.42  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_561])).
% 2.67/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.42  
% 2.67/1.42  Inference rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Ref     : 0
% 2.67/1.42  #Sup     : 115
% 2.67/1.42  #Fact    : 0
% 2.67/1.42  #Define  : 0
% 2.67/1.42  #Split   : 1
% 2.67/1.42  #Chain   : 0
% 2.67/1.42  #Close   : 0
% 2.67/1.42  
% 2.67/1.42  Ordering : KBO
% 2.67/1.42  
% 2.67/1.42  Simplification rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Subsume      : 2
% 2.67/1.42  #Demod        : 30
% 2.67/1.42  #Tautology    : 51
% 2.67/1.42  #SimpNegUnit  : 2
% 2.67/1.42  #BackRed      : 0
% 2.67/1.42  
% 2.67/1.42  #Partial instantiations: 0
% 2.67/1.42  #Strategies tried      : 1
% 2.67/1.42  
% 2.67/1.42  Timing (in seconds)
% 2.67/1.42  ----------------------
% 2.67/1.42  Preprocessing        : 0.32
% 2.67/1.42  Parsing              : 0.17
% 2.67/1.42  CNF conversion       : 0.02
% 2.67/1.42  Main loop            : 0.33
% 2.67/1.42  Inferencing          : 0.12
% 2.67/1.42  Reduction            : 0.11
% 2.67/1.42  Demodulation         : 0.08
% 2.67/1.42  BG Simplification    : 0.02
% 2.67/1.42  Subsumption          : 0.06
% 2.67/1.42  Abstraction          : 0.02
% 2.67/1.42  MUC search           : 0.00
% 2.67/1.42  Cooper               : 0.00
% 2.67/1.42  Total                : 0.68
% 2.67/1.42  Index Insertion      : 0.00
% 2.67/1.42  Index Deletion       : 0.00
% 2.67/1.42  Index Matching       : 0.00
% 2.67/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
