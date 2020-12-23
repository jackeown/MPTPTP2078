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
% DateTime   : Thu Dec  3 09:51:11 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :   57 (  77 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  98 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_89,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_68,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_87,plain,(
    ! [A_103,B_104] : k1_enumset1(A_103,A_103,B_104) = k2_tarski(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,(
    ! [B_104,A_103] : r2_hidden(B_104,k2_tarski(A_103,B_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_18])).

tff(c_116,plain,(
    ! [A_110,B_111] : k3_tarski(k2_tarski(A_110,B_111)) = k2_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(A_82,k3_tarski(B_83))
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7210,plain,(
    ! [A_18020,A_18021,B_18022] :
      ( r1_tarski(A_18020,k2_xboole_0(A_18021,B_18022))
      | ~ r2_hidden(A_18020,k2_tarski(A_18021,B_18022)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_64])).

tff(c_7233,plain,(
    ! [B_104,A_103] : r1_tarski(B_104,k2_xboole_0(A_103,B_104)) ),
    inference(resolution,[status(thm)],[c_96,c_7210])).

tff(c_70,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_152,plain,(
    ! [A_115,B_116] :
      ( r2_xboole_0(A_115,B_116)
      | B_116 = A_115
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r2_xboole_0(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_174,plain,(
    ! [B_120,A_121] :
      ( ~ r1_tarski(B_120,A_121)
      | B_120 = A_121
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(resolution,[status(thm)],[c_152,c_14])).

tff(c_186,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_174])).

tff(c_340,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_7238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7233,c_340])).

tff(c_7239,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_66,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    ! [A_103,B_104] : r2_hidden(A_103,k2_tarski(A_103,B_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_22])).

tff(c_196,plain,(
    ! [C_125,B_126,A_127] :
      ( r2_hidden(C_125,B_126)
      | ~ r2_hidden(C_125,A_127)
      | ~ r1_tarski(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_137,B_138,B_139] :
      ( r2_hidden(A_137,B_138)
      | ~ r1_tarski(k2_tarski(A_137,B_139),B_138) ) ),
    inference(resolution,[status(thm)],[c_93,c_196])).

tff(c_8024,plain,(
    ! [A_18309,B_18310,B_18311] :
      ( r2_hidden(A_18309,k3_tarski(B_18310))
      | ~ r2_hidden(k2_tarski(A_18309,B_18311),B_18310) ) ),
    inference(resolution,[status(thm)],[c_64,c_292])).

tff(c_8100,plain,(
    ! [A_18309,B_18311,B_104] : r2_hidden(A_18309,k3_tarski(k2_tarski(k2_tarski(A_18309,B_18311),B_104))) ),
    inference(resolution,[status(thm)],[c_93,c_8024])).

tff(c_8170,plain,(
    ! [A_18319,B_18320,B_18321] : r2_hidden(A_18319,k2_xboole_0(k2_tarski(A_18319,B_18320),B_18321)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8100])).

tff(c_8187,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7239,c_8170])).

tff(c_8200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:08:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.98/2.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.44  
% 6.98/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.44  %$ r2_xboole_0 > r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.98/2.44  
% 6.98/2.44  %Foreground sorts:
% 6.98/2.44  
% 6.98/2.44  
% 6.98/2.44  %Background operators:
% 6.98/2.44  
% 6.98/2.44  
% 6.98/2.44  %Foreground operators:
% 6.98/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.98/2.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.98/2.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.98/2.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.98/2.44  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.98/2.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.98/2.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.98/2.44  tff('#skF_5', type, '#skF_5': $i).
% 6.98/2.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.98/2.44  tff('#skF_6', type, '#skF_6': $i).
% 6.98/2.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.98/2.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.44  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.98/2.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.98/2.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.98/2.44  tff('#skF_4', type, '#skF_4': $i).
% 6.98/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.98/2.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.98/2.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.98/2.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.98/2.44  
% 6.98/2.45  tff(f_94, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 6.98/2.45  tff(f_73, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.98/2.45  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.98/2.45  tff(f_89, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.98/2.45  tff(f_87, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.98/2.45  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.98/2.45  tff(f_44, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 6.98/2.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.98/2.45  tff(c_68, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.98/2.45  tff(c_87, plain, (![A_103, B_104]: (k1_enumset1(A_103, A_103, B_104)=k2_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.98/2.45  tff(c_18, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.98/2.45  tff(c_96, plain, (![B_104, A_103]: (r2_hidden(B_104, k2_tarski(A_103, B_104)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_18])).
% 6.98/2.45  tff(c_116, plain, (![A_110, B_111]: (k3_tarski(k2_tarski(A_110, B_111))=k2_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.98/2.45  tff(c_64, plain, (![A_82, B_83]: (r1_tarski(A_82, k3_tarski(B_83)) | ~r2_hidden(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.98/2.45  tff(c_7210, plain, (![A_18020, A_18021, B_18022]: (r1_tarski(A_18020, k2_xboole_0(A_18021, B_18022)) | ~r2_hidden(A_18020, k2_tarski(A_18021, B_18022)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_64])).
% 6.98/2.45  tff(c_7233, plain, (![B_104, A_103]: (r1_tarski(B_104, k2_xboole_0(A_103, B_104)))), inference(resolution, [status(thm)], [c_96, c_7210])).
% 6.98/2.45  tff(c_70, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.98/2.45  tff(c_152, plain, (![A_115, B_116]: (r2_xboole_0(A_115, B_116) | B_116=A_115 | ~r1_tarski(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.98/2.45  tff(c_14, plain, (![B_9, A_8]: (~r2_xboole_0(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.98/2.45  tff(c_174, plain, (![B_120, A_121]: (~r1_tarski(B_120, A_121) | B_120=A_121 | ~r1_tarski(A_121, B_120))), inference(resolution, [status(thm)], [c_152, c_14])).
% 6.98/2.45  tff(c_186, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_174])).
% 6.98/2.45  tff(c_340, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_186])).
% 6.98/2.45  tff(c_7238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7233, c_340])).
% 6.98/2.45  tff(c_7239, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_186])).
% 6.98/2.45  tff(c_66, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.98/2.45  tff(c_22, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.98/2.45  tff(c_93, plain, (![A_103, B_104]: (r2_hidden(A_103, k2_tarski(A_103, B_104)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_22])).
% 6.98/2.45  tff(c_196, plain, (![C_125, B_126, A_127]: (r2_hidden(C_125, B_126) | ~r2_hidden(C_125, A_127) | ~r1_tarski(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.98/2.45  tff(c_292, plain, (![A_137, B_138, B_139]: (r2_hidden(A_137, B_138) | ~r1_tarski(k2_tarski(A_137, B_139), B_138))), inference(resolution, [status(thm)], [c_93, c_196])).
% 6.98/2.45  tff(c_8024, plain, (![A_18309, B_18310, B_18311]: (r2_hidden(A_18309, k3_tarski(B_18310)) | ~r2_hidden(k2_tarski(A_18309, B_18311), B_18310))), inference(resolution, [status(thm)], [c_64, c_292])).
% 6.98/2.45  tff(c_8100, plain, (![A_18309, B_18311, B_104]: (r2_hidden(A_18309, k3_tarski(k2_tarski(k2_tarski(A_18309, B_18311), B_104))))), inference(resolution, [status(thm)], [c_93, c_8024])).
% 6.98/2.45  tff(c_8170, plain, (![A_18319, B_18320, B_18321]: (r2_hidden(A_18319, k2_xboole_0(k2_tarski(A_18319, B_18320), B_18321)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8100])).
% 6.98/2.45  tff(c_8187, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7239, c_8170])).
% 6.98/2.45  tff(c_8200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_8187])).
% 6.98/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.45  
% 6.98/2.45  Inference rules
% 6.98/2.45  ----------------------
% 6.98/2.45  #Ref     : 0
% 6.98/2.45  #Sup     : 1009
% 6.98/2.45  #Fact    : 18
% 6.98/2.45  #Define  : 0
% 6.98/2.45  #Split   : 1
% 6.98/2.45  #Chain   : 0
% 6.98/2.45  #Close   : 0
% 6.98/2.45  
% 6.98/2.45  Ordering : KBO
% 6.98/2.45  
% 6.98/2.45  Simplification rules
% 6.98/2.45  ----------------------
% 6.98/2.45  #Subsume      : 104
% 6.98/2.45  #Demod        : 249
% 6.98/2.45  #Tautology    : 280
% 6.98/2.45  #SimpNegUnit  : 1
% 6.98/2.45  #BackRed      : 2
% 6.98/2.45  
% 6.98/2.45  #Partial instantiations: 5202
% 6.98/2.45  #Strategies tried      : 1
% 6.98/2.45  
% 6.98/2.45  Timing (in seconds)
% 6.98/2.45  ----------------------
% 6.98/2.45  Preprocessing        : 0.35
% 6.98/2.46  Parsing              : 0.18
% 6.98/2.46  CNF conversion       : 0.03
% 6.98/2.46  Main loop            : 1.34
% 6.98/2.46  Inferencing          : 0.74
% 6.98/2.46  Reduction            : 0.33
% 6.98/2.46  Demodulation         : 0.25
% 6.98/2.46  BG Simplification    : 0.06
% 6.98/2.46  Subsumption          : 0.16
% 6.98/2.46  Abstraction          : 0.06
% 6.98/2.46  MUC search           : 0.00
% 6.98/2.46  Cooper               : 0.00
% 6.98/2.46  Total                : 1.72
% 6.98/2.46  Index Insertion      : 0.00
% 6.98/2.46  Index Deletion       : 0.00
% 6.98/2.46  Index Matching       : 0.00
% 6.98/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
