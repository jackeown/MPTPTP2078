%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:52 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 157 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    r2_hidden('#skF_4',k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_155,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden(k1_mcart_1(A_66),B_67)
      | ~ r2_hidden(A_66,k2_zfmisc_1(B_67,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_166,plain,(
    r2_hidden(k1_mcart_1('#skF_4'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_155])).

tff(c_75,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | ~ r1_tarski(k1_tarski(A_42),B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    ! [A_42] : r2_hidden(A_42,k1_tarski(A_42)) ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_38,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(k1_tarski(A_25),B_26)
      | r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_196,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,B_76)
      | ~ r2_hidden(C_77,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_204,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,k1_tarski(A_82))
      | r2_hidden(A_82,B_81) ) ),
    inference(resolution,[status(thm)],[c_38,c_196])).

tff(c_233,plain,(
    ! [A_84,A_85] :
      ( ~ r2_hidden(A_84,k1_tarski(A_85))
      | r2_hidden(A_85,k1_tarski(A_84)) ) ),
    inference(resolution,[status(thm)],[c_80,c_204])).

tff(c_244,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_166,c_233])).

tff(c_24,plain,(
    ! [C_22,A_18] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_497,plain,(
    ! [C_113,A_114,A_115] :
      ( ~ r2_hidden(C_113,k1_tarski(A_114))
      | r2_hidden(A_114,k1_zfmisc_1(A_115))
      | ~ r1_tarski(C_113,A_115) ) ),
    inference(resolution,[status(thm)],[c_24,c_204])).

tff(c_555,plain,(
    ! [A_120] :
      ( r2_hidden(k1_mcart_1('#skF_4'),k1_zfmisc_1(A_120))
      | ~ r1_tarski('#skF_5',A_120) ) ),
    inference(resolution,[status(thm)],[c_244,c_497])).

tff(c_22,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_572,plain,(
    ! [A_121] :
      ( r1_tarski(k1_mcart_1('#skF_4'),A_121)
      | ~ r1_tarski('#skF_5',A_121) ) ),
    inference(resolution,[status(thm)],[c_555,c_22])).

tff(c_50,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_4'),'#skF_6')
    | k1_mcart_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_86,plain,(
    k1_mcart_1('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_531,plain,(
    ! [A_116] :
      ( r2_hidden('#skF_5',k1_zfmisc_1(A_116))
      | ~ r1_tarski(k1_mcart_1('#skF_4'),A_116) ) ),
    inference(resolution,[status(thm)],[c_166,c_497])).

tff(c_543,plain,(
    ! [A_117] :
      ( r1_tarski('#skF_5',A_117)
      | ~ r1_tarski(k1_mcart_1('#skF_4'),A_117) ) ),
    inference(resolution,[status(thm)],[c_531,c_22])).

tff(c_548,plain,(
    r1_tarski('#skF_5',k1_mcart_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_543])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_551,plain,
    ( k1_mcart_1('#skF_4') = '#skF_5'
    | ~ r1_tarski(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_548,c_8])).

tff(c_554,plain,(
    ~ r1_tarski(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_551])).

tff(c_575,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_572,c_554])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_575])).

tff(c_589,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_689,plain,(
    ! [A_152,C_153,B_154] :
      ( r2_hidden(k2_mcart_1(A_152),C_153)
      | ~ r2_hidden(A_152,k2_zfmisc_1(B_154,C_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_697,plain,(
    r2_hidden(k2_mcart_1('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_689])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:52:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.40  
% 2.88/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.88/1.40  
% 2.88/1.40  %Foreground sorts:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Background operators:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Foreground operators:
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.88/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.88/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.40  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.88/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.88/1.40  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.88/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.40  
% 2.88/1.41  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.88/1.41  tff(f_94, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.88/1.41  tff(f_87, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.88/1.41  tff(f_68, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.88/1.41  tff(f_73, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.88/1.41  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.88/1.41  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.88/1.41  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.88/1.41  tff(c_52, plain, (r2_hidden('#skF_4', k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.88/1.41  tff(c_155, plain, (![A_66, B_67, C_68]: (r2_hidden(k1_mcart_1(A_66), B_67) | ~r2_hidden(A_66, k2_zfmisc_1(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.41  tff(c_166, plain, (r2_hidden(k1_mcart_1('#skF_4'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_155])).
% 2.88/1.41  tff(c_75, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | ~r1_tarski(k1_tarski(A_42), B_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.88/1.41  tff(c_80, plain, (![A_42]: (r2_hidden(A_42, k1_tarski(A_42)))), inference(resolution, [status(thm)], [c_12, c_75])).
% 2.88/1.41  tff(c_38, plain, (![A_25, B_26]: (r1_xboole_0(k1_tarski(A_25), B_26) | r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.41  tff(c_196, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, B_76) | ~r2_hidden(C_77, A_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.41  tff(c_204, plain, (![C_80, B_81, A_82]: (~r2_hidden(C_80, B_81) | ~r2_hidden(C_80, k1_tarski(A_82)) | r2_hidden(A_82, B_81))), inference(resolution, [status(thm)], [c_38, c_196])).
% 2.88/1.41  tff(c_233, plain, (![A_84, A_85]: (~r2_hidden(A_84, k1_tarski(A_85)) | r2_hidden(A_85, k1_tarski(A_84)))), inference(resolution, [status(thm)], [c_80, c_204])).
% 2.88/1.41  tff(c_244, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_4')))), inference(resolution, [status(thm)], [c_166, c_233])).
% 2.88/1.41  tff(c_24, plain, (![C_22, A_18]: (r2_hidden(C_22, k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.88/1.41  tff(c_497, plain, (![C_113, A_114, A_115]: (~r2_hidden(C_113, k1_tarski(A_114)) | r2_hidden(A_114, k1_zfmisc_1(A_115)) | ~r1_tarski(C_113, A_115))), inference(resolution, [status(thm)], [c_24, c_204])).
% 2.88/1.41  tff(c_555, plain, (![A_120]: (r2_hidden(k1_mcart_1('#skF_4'), k1_zfmisc_1(A_120)) | ~r1_tarski('#skF_5', A_120))), inference(resolution, [status(thm)], [c_244, c_497])).
% 2.88/1.41  tff(c_22, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.88/1.41  tff(c_572, plain, (![A_121]: (r1_tarski(k1_mcart_1('#skF_4'), A_121) | ~r1_tarski('#skF_5', A_121))), inference(resolution, [status(thm)], [c_555, c_22])).
% 2.88/1.41  tff(c_50, plain, (~r2_hidden(k2_mcart_1('#skF_4'), '#skF_6') | k1_mcart_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.88/1.41  tff(c_86, plain, (k1_mcart_1('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_50])).
% 2.88/1.41  tff(c_531, plain, (![A_116]: (r2_hidden('#skF_5', k1_zfmisc_1(A_116)) | ~r1_tarski(k1_mcart_1('#skF_4'), A_116))), inference(resolution, [status(thm)], [c_166, c_497])).
% 2.88/1.41  tff(c_543, plain, (![A_117]: (r1_tarski('#skF_5', A_117) | ~r1_tarski(k1_mcart_1('#skF_4'), A_117))), inference(resolution, [status(thm)], [c_531, c_22])).
% 2.88/1.41  tff(c_548, plain, (r1_tarski('#skF_5', k1_mcart_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_543])).
% 2.88/1.41  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.88/1.41  tff(c_551, plain, (k1_mcart_1('#skF_4')='#skF_5' | ~r1_tarski(k1_mcart_1('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_548, c_8])).
% 2.88/1.41  tff(c_554, plain, (~r1_tarski(k1_mcart_1('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_551])).
% 2.88/1.41  tff(c_575, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_572, c_554])).
% 2.88/1.41  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_575])).
% 2.88/1.41  tff(c_589, plain, (~r2_hidden(k2_mcart_1('#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 2.88/1.41  tff(c_689, plain, (![A_152, C_153, B_154]: (r2_hidden(k2_mcart_1(A_152), C_153) | ~r2_hidden(A_152, k2_zfmisc_1(B_154, C_153)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.41  tff(c_697, plain, (r2_hidden(k2_mcart_1('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_52, c_689])).
% 2.88/1.41  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_589, c_697])).
% 2.88/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  Inference rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Ref     : 0
% 2.88/1.41  #Sup     : 147
% 2.88/1.41  #Fact    : 0
% 2.88/1.41  #Define  : 0
% 2.88/1.41  #Split   : 4
% 2.88/1.41  #Chain   : 0
% 2.88/1.41  #Close   : 0
% 2.88/1.41  
% 2.88/1.41  Ordering : KBO
% 2.88/1.41  
% 2.88/1.41  Simplification rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Subsume      : 10
% 2.88/1.41  #Demod        : 17
% 2.88/1.41  #Tautology    : 33
% 2.88/1.41  #SimpNegUnit  : 2
% 2.88/1.41  #BackRed      : 0
% 2.88/1.41  
% 2.88/1.41  #Partial instantiations: 0
% 2.88/1.41  #Strategies tried      : 1
% 2.88/1.41  
% 2.88/1.41  Timing (in seconds)
% 2.88/1.41  ----------------------
% 2.88/1.41  Preprocessing        : 0.31
% 2.88/1.42  Parsing              : 0.16
% 2.88/1.42  CNF conversion       : 0.02
% 2.88/1.42  Main loop            : 0.35
% 2.88/1.42  Inferencing          : 0.13
% 2.88/1.42  Reduction            : 0.09
% 2.88/1.42  Demodulation         : 0.06
% 2.88/1.42  BG Simplification    : 0.02
% 2.88/1.42  Subsumption          : 0.07
% 2.88/1.42  Abstraction          : 0.02
% 2.88/1.42  MUC search           : 0.00
% 2.88/1.42  Cooper               : 0.00
% 2.88/1.42  Total                : 0.68
% 2.88/1.42  Index Insertion      : 0.00
% 2.88/1.42  Index Deletion       : 0.00
% 2.88/1.42  Index Matching       : 0.00
% 2.88/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
