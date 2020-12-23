%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:54 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   56 (  67 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  77 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_55,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_36,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_106,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_126,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k1_mcart_1(A_62),B_63)
      | ~ r2_hidden(A_62,k2_zfmisc_1(B_63,C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_128,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_126])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_128])).

tff(c_133,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_168,plain,(
    ! [A_79,C_80,B_81] :
      ( r2_hidden(k2_mcart_1(A_79),C_80)
      | ~ r2_hidden(A_79,k2_zfmisc_1(B_81,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_171,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_168])).

tff(c_28,plain,(
    ! [A_37] : k1_setfam_1(k1_tarski(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_135,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(k1_setfam_1(B_65),A_66)
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,(
    ! [A_37,A_66] :
      ( r1_tarski(A_37,A_66)
      | ~ r2_hidden(A_66,k1_tarski(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_135])).

tff(c_188,plain,(
    r1_tarski('#skF_3',k2_mcart_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_171,c_138])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [A_5] : k3_tarski(k1_tarski(A_5)) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_78])).

tff(c_94,plain,(
    ! [A_53] : k3_tarski(k1_tarski(A_53)) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_24,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,k3_tarski(B_34))
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,(
    ! [A_33,A_53] :
      ( r1_tarski(A_33,A_53)
      | ~ r2_hidden(A_33,k1_tarski(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_24])).

tff(c_187,plain,(
    r1_tarski(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_100])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_195,plain,
    ( k2_mcart_1('#skF_1') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_mcart_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_187,c_4])).

tff(c_198,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_195])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n024.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.32  % CPULimit   : 60
% 0.17/0.32  % DateTime   : Tue Dec  1 09:30:51 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.30  
% 1.95/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.30  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.30  
% 1.95/1.30  %Foreground sorts:
% 1.95/1.30  
% 1.95/1.30  
% 1.95/1.30  %Background operators:
% 1.95/1.30  
% 1.95/1.30  
% 1.95/1.30  %Foreground operators:
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.95/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.95/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.95/1.30  
% 2.18/1.31  tff(f_72, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 2.18/1.31  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.18/1.31  tff(f_55, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.18/1.31  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.18/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.18/1.31  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.31  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.18/1.31  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.18/1.31  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.18/1.31  tff(c_36, plain, (k2_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.31  tff(c_106, plain, (~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 2.18/1.31  tff(c_38, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.31  tff(c_126, plain, (![A_62, B_63, C_64]: (r2_hidden(k1_mcart_1(A_62), B_63) | ~r2_hidden(A_62, k2_zfmisc_1(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.18/1.31  tff(c_128, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_38, c_126])).
% 2.18/1.31  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_128])).
% 2.18/1.31  tff(c_133, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.18/1.31  tff(c_168, plain, (![A_79, C_80, B_81]: (r2_hidden(k2_mcart_1(A_79), C_80) | ~r2_hidden(A_79, k2_zfmisc_1(B_81, C_80)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.18/1.31  tff(c_171, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_168])).
% 2.18/1.31  tff(c_28, plain, (![A_37]: (k1_setfam_1(k1_tarski(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.31  tff(c_135, plain, (![B_65, A_66]: (r1_tarski(k1_setfam_1(B_65), A_66) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.31  tff(c_138, plain, (![A_37, A_66]: (r1_tarski(A_37, A_66) | ~r2_hidden(A_66, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_135])).
% 2.18/1.31  tff(c_188, plain, (r1_tarski('#skF_3', k2_mcart_1('#skF_1'))), inference(resolution, [status(thm)], [c_171, c_138])).
% 2.18/1.31  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.31  tff(c_10, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.31  tff(c_78, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.31  tff(c_90, plain, (![A_5]: (k3_tarski(k1_tarski(A_5))=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_10, c_78])).
% 2.18/1.31  tff(c_94, plain, (![A_53]: (k3_tarski(k1_tarski(A_53))=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_90])).
% 2.18/1.31  tff(c_24, plain, (![A_33, B_34]: (r1_tarski(A_33, k3_tarski(B_34)) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.31  tff(c_100, plain, (![A_33, A_53]: (r1_tarski(A_33, A_53) | ~r2_hidden(A_33, k1_tarski(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_24])).
% 2.18/1.31  tff(c_187, plain, (r1_tarski(k2_mcart_1('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_171, c_100])).
% 2.18/1.31  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.31  tff(c_195, plain, (k2_mcart_1('#skF_1')='#skF_3' | ~r1_tarski('#skF_3', k2_mcart_1('#skF_1'))), inference(resolution, [status(thm)], [c_187, c_4])).
% 2.18/1.31  tff(c_198, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_195])).
% 2.18/1.31  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_198])).
% 2.18/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  Inference rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Ref     : 0
% 2.18/1.31  #Sup     : 34
% 2.18/1.31  #Fact    : 0
% 2.18/1.31  #Define  : 0
% 2.18/1.31  #Split   : 1
% 2.18/1.31  #Chain   : 0
% 2.18/1.31  #Close   : 0
% 2.18/1.31  
% 2.18/1.31  Ordering : KBO
% 2.18/1.31  
% 2.18/1.31  Simplification rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Subsume      : 0
% 2.18/1.31  #Demod        : 6
% 2.18/1.31  #Tautology    : 20
% 2.18/1.31  #SimpNegUnit  : 3
% 2.18/1.31  #BackRed      : 0
% 2.18/1.31  
% 2.18/1.31  #Partial instantiations: 0
% 2.18/1.31  #Strategies tried      : 1
% 2.18/1.31  
% 2.18/1.31  Timing (in seconds)
% 2.18/1.31  ----------------------
% 2.18/1.31  Preprocessing        : 0.35
% 2.18/1.31  Parsing              : 0.19
% 2.18/1.31  CNF conversion       : 0.02
% 2.18/1.31  Main loop            : 0.16
% 2.18/1.31  Inferencing          : 0.06
% 2.18/1.31  Reduction            : 0.05
% 2.18/1.31  Demodulation         : 0.04
% 2.18/1.31  BG Simplification    : 0.01
% 2.18/1.32  Subsumption          : 0.02
% 2.18/1.32  Abstraction          : 0.01
% 2.18/1.32  MUC search           : 0.00
% 2.18/1.32  Cooper               : 0.00
% 2.18/1.32  Total                : 0.54
% 2.18/1.32  Index Insertion      : 0.00
% 2.18/1.32  Index Deletion       : 0.00
% 2.18/1.32  Index Matching       : 0.00
% 2.18/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
