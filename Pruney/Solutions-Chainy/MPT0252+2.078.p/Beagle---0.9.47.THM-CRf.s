%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:10 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  72 expanded)
%              Number of equality atoms :   12 (  23 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_62,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_115,plain,(
    ! [A_80,B_81] : k1_enumset1(A_80,A_80,B_81) = k2_tarski(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_121,plain,(
    ! [B_81,A_80] : r2_hidden(B_81,k2_tarski(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_10])).

tff(c_54,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,k3_tarski(B_79))
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1573,plain,(
    ! [A_286,A_287,B_288] :
      ( r1_tarski(A_286,k2_xboole_0(A_287,B_288))
      | ~ r2_hidden(A_286,k2_tarski(A_287,B_288)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_108])).

tff(c_1589,plain,(
    ! [B_81,A_80] : r1_tarski(B_81,k2_xboole_0(A_80,B_81)) ),
    inference(resolution,[status(thm)],[c_121,c_1573])).

tff(c_64,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_144,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,
    ( k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_144])).

tff(c_199,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_1630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_199])).

tff(c_1631,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_12,plain,(
    ! [E_9,A_3,C_5] : r2_hidden(E_9,k1_enumset1(A_3,E_9,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    ! [A_80,B_81] : r2_hidden(A_80,k2_tarski(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_12])).

tff(c_52,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,k3_tarski(B_58))
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_184,plain,(
    ! [A_94,C_95,B_96] :
      ( r2_hidden(A_94,C_95)
      | ~ r1_tarski(k2_tarski(A_94,B_96),C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1842,plain,(
    ! [A_326,B_327,B_328] :
      ( r2_hidden(A_326,k3_tarski(B_327))
      | ~ r2_hidden(k2_tarski(A_326,B_328),B_327) ) ),
    inference(resolution,[status(thm)],[c_52,c_184])).

tff(c_1882,plain,(
    ! [A_326,B_328,B_81] : r2_hidden(A_326,k3_tarski(k2_tarski(k2_tarski(A_326,B_328),B_81))) ),
    inference(resolution,[status(thm)],[c_124,c_1842])).

tff(c_1923,plain,(
    ! [A_329,B_330,B_331] : r2_hidden(A_329,k2_xboole_0(k2_tarski(A_329,B_330),B_331)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1882])).

tff(c_1934,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1631,c_1923])).

tff(c_1945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:22:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.59  
% 3.67/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.60  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.67/1.60  
% 3.67/1.60  %Foreground sorts:
% 3.67/1.60  
% 3.67/1.60  
% 3.67/1.60  %Background operators:
% 3.67/1.60  
% 3.67/1.60  
% 3.67/1.60  %Foreground operators:
% 3.67/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.67/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.67/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.67/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.67/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.67/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.67/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.67/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.67/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.67/1.60  
% 3.67/1.61  tff(f_83, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 3.67/1.61  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.67/1.61  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.67/1.61  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.67/1.61  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.67/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.67/1.61  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.67/1.61  tff(c_62, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.67/1.61  tff(c_115, plain, (![A_80, B_81]: (k1_enumset1(A_80, A_80, B_81)=k2_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.67/1.61  tff(c_10, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.67/1.61  tff(c_121, plain, (![B_81, A_80]: (r2_hidden(B_81, k2_tarski(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_10])).
% 3.67/1.61  tff(c_54, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.67/1.61  tff(c_108, plain, (![A_78, B_79]: (r1_tarski(A_78, k3_tarski(B_79)) | ~r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.67/1.61  tff(c_1573, plain, (![A_286, A_287, B_288]: (r1_tarski(A_286, k2_xboole_0(A_287, B_288)) | ~r2_hidden(A_286, k2_tarski(A_287, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_108])).
% 3.67/1.61  tff(c_1589, plain, (![B_81, A_80]: (r1_tarski(B_81, k2_xboole_0(A_80, B_81)))), inference(resolution, [status(thm)], [c_121, c_1573])).
% 3.67/1.61  tff(c_64, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.67/1.61  tff(c_144, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.67/1.61  tff(c_151, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_144])).
% 3.67/1.61  tff(c_199, plain, (~r1_tarski('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_151])).
% 3.67/1.61  tff(c_1630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1589, c_199])).
% 3.67/1.61  tff(c_1631, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_151])).
% 3.67/1.61  tff(c_12, plain, (![E_9, A_3, C_5]: (r2_hidden(E_9, k1_enumset1(A_3, E_9, C_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.67/1.61  tff(c_124, plain, (![A_80, B_81]: (r2_hidden(A_80, k2_tarski(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_12])).
% 3.67/1.61  tff(c_52, plain, (![A_57, B_58]: (r1_tarski(A_57, k3_tarski(B_58)) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.67/1.61  tff(c_184, plain, (![A_94, C_95, B_96]: (r2_hidden(A_94, C_95) | ~r1_tarski(k2_tarski(A_94, B_96), C_95))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.67/1.61  tff(c_1842, plain, (![A_326, B_327, B_328]: (r2_hidden(A_326, k3_tarski(B_327)) | ~r2_hidden(k2_tarski(A_326, B_328), B_327))), inference(resolution, [status(thm)], [c_52, c_184])).
% 3.67/1.61  tff(c_1882, plain, (![A_326, B_328, B_81]: (r2_hidden(A_326, k3_tarski(k2_tarski(k2_tarski(A_326, B_328), B_81))))), inference(resolution, [status(thm)], [c_124, c_1842])).
% 3.67/1.61  tff(c_1923, plain, (![A_329, B_330, B_331]: (r2_hidden(A_329, k2_xboole_0(k2_tarski(A_329, B_330), B_331)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1882])).
% 3.67/1.61  tff(c_1934, plain, (r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1631, c_1923])).
% 3.67/1.61  tff(c_1945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1934])).
% 3.67/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.61  
% 3.67/1.61  Inference rules
% 3.67/1.61  ----------------------
% 3.67/1.61  #Ref     : 0
% 3.67/1.61  #Sup     : 388
% 3.67/1.61  #Fact    : 0
% 3.67/1.61  #Define  : 0
% 3.67/1.61  #Split   : 1
% 3.67/1.61  #Chain   : 0
% 3.67/1.61  #Close   : 0
% 3.67/1.61  
% 3.67/1.61  Ordering : KBO
% 3.67/1.61  
% 3.67/1.61  Simplification rules
% 3.67/1.61  ----------------------
% 3.67/1.61  #Subsume      : 8
% 3.67/1.61  #Demod        : 144
% 3.67/1.61  #Tautology    : 170
% 3.67/1.61  #SimpNegUnit  : 1
% 3.67/1.61  #BackRed      : 2
% 3.67/1.61  
% 3.67/1.61  #Partial instantiations: 0
% 3.67/1.61  #Strategies tried      : 1
% 3.67/1.61  
% 3.67/1.61  Timing (in seconds)
% 3.67/1.61  ----------------------
% 3.67/1.61  Preprocessing        : 0.33
% 3.67/1.61  Parsing              : 0.17
% 3.67/1.61  CNF conversion       : 0.02
% 3.67/1.61  Main loop            : 0.53
% 3.67/1.61  Inferencing          : 0.19
% 3.67/1.61  Reduction            : 0.18
% 3.67/1.61  Demodulation         : 0.14
% 3.67/1.61  BG Simplification    : 0.03
% 3.67/1.61  Subsumption          : 0.10
% 3.67/1.61  Abstraction          : 0.03
% 3.67/1.61  MUC search           : 0.00
% 3.67/1.61  Cooper               : 0.00
% 3.67/1.61  Total                : 0.89
% 3.67/1.61  Index Insertion      : 0.00
% 3.67/1.61  Index Deletion       : 0.00
% 3.67/1.61  Index Matching       : 0.00
% 3.67/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
