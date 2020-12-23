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
% DateTime   : Thu Dec  3 09:55:13 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 6.75s
% Verified   : 
% Statistics : Number of formulae       :   65 (  77 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 129 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_110,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_109,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(A_43,B_44)
      | k4_xboole_0(A_43,B_44) != A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [B_44,A_43] :
      ( r1_xboole_0(B_44,A_43)
      | k4_xboole_0(A_43,B_44) != A_43 ) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_44,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_60,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_1184,plain,(
    ! [A_126,C_127,B_128] :
      ( ~ r1_xboole_0(A_126,C_127)
      | ~ r1_xboole_0(A_126,B_128)
      | r1_xboole_0(A_126,k2_xboole_0(B_128,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4392,plain,(
    ! [B_231,C_232,A_233] :
      ( r1_xboole_0(k2_xboole_0(B_231,C_232),A_233)
      | ~ r1_xboole_0(A_233,C_232)
      | ~ r1_xboole_0(A_233,B_231) ) ),
    inference(resolution,[status(thm)],[c_1184,c_4])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4427,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4392,c_42])).

tff(c_4440,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4427])).

tff(c_4451,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_115,c_4440])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_937,plain,(
    ! [A_107,B_108,C_109] :
      ( ~ r1_xboole_0(A_107,B_108)
      | ~ r2_hidden(C_109,B_108)
      | ~ r2_hidden(C_109,A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1016,plain,(
    ! [C_110] :
      ( ~ r2_hidden(C_110,'#skF_4')
      | ~ r2_hidden(C_110,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_937])).

tff(c_1030,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1016])).

tff(c_394,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,k1_tarski(B_66)) = A_65
      | r2_hidden(B_66,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_409,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(A_65,k1_tarski(B_66))
      | r2_hidden(B_66,A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_563,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_581,plain,(
    ! [A_76,B_77,A_5] :
      ( ~ r1_xboole_0(A_76,B_77)
      | r1_xboole_0(A_5,k3_xboole_0(A_76,B_77)) ) ),
    inference(resolution,[status(thm)],[c_8,c_563])).

tff(c_1566,plain,(
    ! [A_148,B_149,C_150] :
      ( ~ r1_xboole_0(A_148,k3_xboole_0(B_149,C_150))
      | ~ r1_tarski(A_148,C_150)
      | r1_xboole_0(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8807,plain,(
    ! [A_343,B_344,A_345] :
      ( ~ r1_tarski(A_343,B_344)
      | r1_xboole_0(A_343,A_345)
      | ~ r1_xboole_0(A_345,B_344) ) ),
    inference(resolution,[status(thm)],[c_581,c_1566])).

tff(c_8811,plain,(
    ! [A_346] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_346)
      | ~ r1_xboole_0(A_346,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_49,c_8807])).

tff(c_8905,plain,(
    ! [A_347] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_347)
      | r2_hidden('#skF_6',A_347) ) ),
    inference(resolution,[status(thm)],[c_409,c_8811])).

tff(c_215,plain,(
    ! [A_55,B_56] :
      ( ~ r1_xboole_0(k3_xboole_0(A_55,B_56),B_56)
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_229,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(k3_xboole_0(A_1,B_2),A_1)
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_215])).

tff(c_8941,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_8905,c_229])).

tff(c_8979,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1030,c_8941])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8994,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8979,c_30])).

tff(c_9001,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4451,c_8994])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:28:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.49  
% 6.75/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.75/2.49  
% 6.75/2.49  %Foreground sorts:
% 6.75/2.49  
% 6.75/2.49  
% 6.75/2.49  %Background operators:
% 6.75/2.49  
% 6.75/2.49  
% 6.75/2.49  %Foreground operators:
% 6.75/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.75/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.75/2.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.75/2.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.75/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.75/2.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.75/2.49  tff('#skF_5', type, '#skF_5': $i).
% 6.75/2.49  tff('#skF_6', type, '#skF_6': $i).
% 6.75/2.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.75/2.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.75/2.49  tff('#skF_3', type, '#skF_3': $i).
% 6.75/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.75/2.49  tff('#skF_4', type, '#skF_4': $i).
% 6.75/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.75/2.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.75/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.75/2.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.75/2.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.75/2.49  
% 6.75/2.50  tff(f_101, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.75/2.50  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.75/2.50  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.75/2.50  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.75/2.50  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.75/2.50  tff(f_110, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.75/2.50  tff(f_97, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.75/2.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.75/2.50  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.75/2.50  tff(f_95, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 6.75/2.50  tff(f_87, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 6.75/2.50  tff(c_109, plain, (![A_43, B_44]: (r1_xboole_0(A_43, B_44) | k4_xboole_0(A_43, B_44)!=A_43)), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.75/2.50  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.75/2.50  tff(c_115, plain, (![B_44, A_43]: (r1_xboole_0(B_44, A_43) | k4_xboole_0(A_43, B_44)!=A_43)), inference(resolution, [status(thm)], [c_109, c_4])).
% 6.75/2.50  tff(c_44, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.75/2.50  tff(c_60, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.75/2.50  tff(c_66, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_60])).
% 6.75/2.50  tff(c_1184, plain, (![A_126, C_127, B_128]: (~r1_xboole_0(A_126, C_127) | ~r1_xboole_0(A_126, B_128) | r1_xboole_0(A_126, k2_xboole_0(B_128, C_127)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.75/2.50  tff(c_4392, plain, (![B_231, C_232, A_233]: (r1_xboole_0(k2_xboole_0(B_231, C_232), A_233) | ~r1_xboole_0(A_233, C_232) | ~r1_xboole_0(A_233, B_231))), inference(resolution, [status(thm)], [c_1184, c_4])).
% 6.75/2.50  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.75/2.50  tff(c_4427, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4392, c_42])).
% 6.75/2.50  tff(c_4440, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4427])).
% 6.75/2.50  tff(c_4451, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(resolution, [status(thm)], [c_115, c_4440])).
% 6.75/2.50  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.75/2.50  tff(c_937, plain, (![A_107, B_108, C_109]: (~r1_xboole_0(A_107, B_108) | ~r2_hidden(C_109, B_108) | ~r2_hidden(C_109, A_107))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.75/2.50  tff(c_1016, plain, (![C_110]: (~r2_hidden(C_110, '#skF_4') | ~r2_hidden(C_110, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_937])).
% 6.75/2.50  tff(c_1030, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_1016])).
% 6.75/2.50  tff(c_394, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k1_tarski(B_66))=A_65 | r2_hidden(B_66, A_65))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.75/2.50  tff(c_28, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.75/2.50  tff(c_409, plain, (![A_65, B_66]: (r1_xboole_0(A_65, k1_tarski(B_66)) | r2_hidden(B_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_394, c_28])).
% 6.75/2.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.75/2.50  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.75/2.50  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 6.75/2.50  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.75/2.50  tff(c_563, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.75/2.50  tff(c_581, plain, (![A_76, B_77, A_5]: (~r1_xboole_0(A_76, B_77) | r1_xboole_0(A_5, k3_xboole_0(A_76, B_77)))), inference(resolution, [status(thm)], [c_8, c_563])).
% 6.75/2.50  tff(c_1566, plain, (![A_148, B_149, C_150]: (~r1_xboole_0(A_148, k3_xboole_0(B_149, C_150)) | ~r1_tarski(A_148, C_150) | r1_xboole_0(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.75/2.50  tff(c_8807, plain, (![A_343, B_344, A_345]: (~r1_tarski(A_343, B_344) | r1_xboole_0(A_343, A_345) | ~r1_xboole_0(A_345, B_344))), inference(resolution, [status(thm)], [c_581, c_1566])).
% 6.75/2.50  tff(c_8811, plain, (![A_346]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_346) | ~r1_xboole_0(A_346, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_49, c_8807])).
% 6.75/2.50  tff(c_8905, plain, (![A_347]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_347) | r2_hidden('#skF_6', A_347))), inference(resolution, [status(thm)], [c_409, c_8811])).
% 6.75/2.50  tff(c_215, plain, (![A_55, B_56]: (~r1_xboole_0(k3_xboole_0(A_55, B_56), B_56) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.75/2.50  tff(c_229, plain, (![A_1, B_2]: (~r1_xboole_0(k3_xboole_0(A_1, B_2), A_1) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_215])).
% 6.75/2.50  tff(c_8941, plain, (r1_xboole_0('#skF_3', '#skF_4') | r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_8905, c_229])).
% 6.75/2.50  tff(c_8979, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1030, c_8941])).
% 6.75/2.50  tff(c_30, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.75/2.50  tff(c_8994, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_8979, c_30])).
% 6.75/2.50  tff(c_9001, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4451, c_8994])).
% 6.75/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.50  
% 6.75/2.50  Inference rules
% 6.75/2.50  ----------------------
% 6.75/2.50  #Ref     : 0
% 6.75/2.50  #Sup     : 2158
% 6.75/2.50  #Fact    : 0
% 6.75/2.50  #Define  : 0
% 6.75/2.50  #Split   : 7
% 6.75/2.50  #Chain   : 0
% 6.75/2.50  #Close   : 0
% 6.75/2.50  
% 6.75/2.50  Ordering : KBO
% 6.75/2.50  
% 6.75/2.50  Simplification rules
% 6.75/2.50  ----------------------
% 6.75/2.50  #Subsume      : 361
% 6.75/2.50  #Demod        : 1154
% 6.75/2.50  #Tautology    : 939
% 6.75/2.50  #SimpNegUnit  : 41
% 6.75/2.50  #BackRed      : 4
% 6.75/2.50  
% 6.75/2.50  #Partial instantiations: 0
% 6.75/2.50  #Strategies tried      : 1
% 6.75/2.50  
% 6.75/2.50  Timing (in seconds)
% 6.75/2.50  ----------------------
% 6.75/2.51  Preprocessing        : 0.32
% 6.75/2.51  Parsing              : 0.16
% 6.75/2.51  CNF conversion       : 0.02
% 6.75/2.51  Main loop            : 1.43
% 6.75/2.51  Inferencing          : 0.41
% 6.75/2.51  Reduction            : 0.58
% 6.75/2.51  Demodulation         : 0.45
% 6.75/2.51  BG Simplification    : 0.04
% 6.75/2.51  Subsumption          : 0.30
% 6.75/2.51  Abstraction          : 0.06
% 6.75/2.51  MUC search           : 0.00
% 6.75/2.51  Cooper               : 0.00
% 6.75/2.51  Total                : 1.78
% 6.75/2.51  Index Insertion      : 0.00
% 6.75/2.51  Index Deletion       : 0.00
% 6.75/2.51  Index Matching       : 0.00
% 6.75/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
