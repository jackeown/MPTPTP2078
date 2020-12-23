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
% DateTime   : Thu Dec  3 09:50:33 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   56 (  67 expanded)
%              Number of leaves         :   32 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  60 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_72,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_208,plain,(
    ! [A_87,B_88] : k3_tarski(k2_tarski(A_87,B_88)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_264,plain,(
    ! [A_97,B_98] : k3_tarski(k2_tarski(A_97,B_98)) = k2_xboole_0(B_98,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_208])).

tff(c_70,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_270,plain,(
    ! [B_98,A_97] : k2_xboole_0(B_98,A_97) = k2_xboole_0(A_97,B_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_70])).

tff(c_74,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_307,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k1_tarski('#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_74])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_365,plain,
    ( k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_307,c_14])).

tff(c_368,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_365])).

tff(c_308,plain,(
    ! [B_101,A_102] : k2_xboole_0(B_101,A_102) = k2_xboole_0(A_102,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_70])).

tff(c_323,plain,(
    ! [A_102,B_101] : r1_tarski(A_102,k2_xboole_0(B_101,A_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_22])).

tff(c_374,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_323])).

tff(c_56,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_190,plain,(
    ! [A_85,B_86] : k1_enumset1(A_85,A_85,B_86) = k2_tarski(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [E_32,A_26,C_28] : r2_hidden(E_32,k1_enumset1(A_26,E_32,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_236,plain,(
    ! [A_90,B_91] : r2_hidden(A_90,k2_tarski(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_36])).

tff(c_245,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_236])).

tff(c_403,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_427,plain,(
    ! [A_113,B_114] :
      ( r2_hidden(A_113,B_114)
      | ~ r1_tarski(k1_tarski(A_113),B_114) ) ),
    inference(resolution,[status(thm)],[c_245,c_403])).

tff(c_430,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_374,c_427])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.34  
% 2.40/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.34  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.40/1.34  
% 2.40/1.34  %Foreground sorts:
% 2.40/1.34  
% 2.40/1.34  
% 2.40/1.34  %Background operators:
% 2.40/1.34  
% 2.40/1.34  
% 2.40/1.34  %Foreground operators:
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.40/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.40/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.40/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.40/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.40/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.34  
% 2.40/1.36  tff(f_92, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.40/1.36  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.40/1.36  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.40/1.36  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.40/1.36  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.40/1.36  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.40/1.36  tff(f_75, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.40/1.36  tff(f_71, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.40/1.36  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.40/1.36  tff(c_72, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.36  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.36  tff(c_30, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.36  tff(c_208, plain, (![A_87, B_88]: (k3_tarski(k2_tarski(A_87, B_88))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.40/1.36  tff(c_264, plain, (![A_97, B_98]: (k3_tarski(k2_tarski(A_97, B_98))=k2_xboole_0(B_98, A_97))), inference(superposition, [status(thm), theory('equality')], [c_30, c_208])).
% 2.40/1.36  tff(c_70, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.40/1.36  tff(c_270, plain, (![B_98, A_97]: (k2_xboole_0(B_98, A_97)=k2_xboole_0(A_97, B_98))), inference(superposition, [status(thm), theory('equality')], [c_264, c_70])).
% 2.40/1.36  tff(c_74, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.36  tff(c_307, plain, (r1_tarski(k2_xboole_0('#skF_5', k1_tarski('#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_74])).
% 2.40/1.36  tff(c_14, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.40/1.36  tff(c_365, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_307, c_14])).
% 2.40/1.36  tff(c_368, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_365])).
% 2.40/1.36  tff(c_308, plain, (![B_101, A_102]: (k2_xboole_0(B_101, A_102)=k2_xboole_0(A_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_264, c_70])).
% 2.40/1.36  tff(c_323, plain, (![A_102, B_101]: (r1_tarski(A_102, k2_xboole_0(B_101, A_102)))), inference(superposition, [status(thm), theory('equality')], [c_308, c_22])).
% 2.40/1.36  tff(c_374, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_368, c_323])).
% 2.40/1.36  tff(c_56, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.36  tff(c_190, plain, (![A_85, B_86]: (k1_enumset1(A_85, A_85, B_86)=k2_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.40/1.36  tff(c_36, plain, (![E_32, A_26, C_28]: (r2_hidden(E_32, k1_enumset1(A_26, E_32, C_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.40/1.36  tff(c_236, plain, (![A_90, B_91]: (r2_hidden(A_90, k2_tarski(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_190, c_36])).
% 2.40/1.36  tff(c_245, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_236])).
% 2.40/1.36  tff(c_403, plain, (![C_110, B_111, A_112]: (r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.40/1.36  tff(c_427, plain, (![A_113, B_114]: (r2_hidden(A_113, B_114) | ~r1_tarski(k1_tarski(A_113), B_114))), inference(resolution, [status(thm)], [c_245, c_403])).
% 2.40/1.36  tff(c_430, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_374, c_427])).
% 2.40/1.36  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_430])).
% 2.40/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.36  
% 2.40/1.36  Inference rules
% 2.40/1.36  ----------------------
% 2.40/1.36  #Ref     : 0
% 2.40/1.36  #Sup     : 89
% 2.40/1.36  #Fact    : 0
% 2.40/1.36  #Define  : 0
% 2.40/1.36  #Split   : 1
% 2.40/1.36  #Chain   : 0
% 2.40/1.36  #Close   : 0
% 2.40/1.36  
% 2.40/1.36  Ordering : KBO
% 2.40/1.36  
% 2.40/1.36  Simplification rules
% 2.40/1.36  ----------------------
% 2.40/1.36  #Subsume      : 1
% 2.40/1.36  #Demod        : 30
% 2.40/1.36  #Tautology    : 66
% 2.40/1.36  #SimpNegUnit  : 1
% 2.40/1.36  #BackRed      : 2
% 2.40/1.36  
% 2.40/1.36  #Partial instantiations: 0
% 2.40/1.36  #Strategies tried      : 1
% 2.40/1.36  
% 2.40/1.36  Timing (in seconds)
% 2.40/1.36  ----------------------
% 2.40/1.36  Preprocessing        : 0.36
% 2.40/1.36  Parsing              : 0.18
% 2.40/1.36  CNF conversion       : 0.03
% 2.40/1.36  Main loop            : 0.24
% 2.40/1.36  Inferencing          : 0.08
% 2.40/1.36  Reduction            : 0.09
% 2.40/1.36  Demodulation         : 0.07
% 2.40/1.36  BG Simplification    : 0.02
% 2.40/1.36  Subsumption          : 0.05
% 2.40/1.36  Abstraction          : 0.02
% 2.40/1.36  MUC search           : 0.00
% 2.40/1.36  Cooper               : 0.00
% 2.40/1.36  Total                : 0.63
% 2.40/1.36  Index Insertion      : 0.00
% 2.40/1.36  Index Deletion       : 0.00
% 2.40/1.36  Index Matching       : 0.00
% 2.40/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
