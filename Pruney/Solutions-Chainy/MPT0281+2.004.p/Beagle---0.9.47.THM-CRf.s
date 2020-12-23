%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:26 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :   47 (  77 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 128 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)) = k1_zfmisc_1(k2_xboole_0(A,B))
       => r3_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_54,plain,(
    ! [A_22,B_23] :
      ( ~ r1_tarski(A_22,B_23)
      | r3_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    ~ r3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_48])).

tff(c_59,plain,(
    ! [B_24,A_25] :
      ( ~ r1_tarski(B_24,A_25)
      | r3_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_59,c_48])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    ! [C_20,A_16] :
      ( r2_hidden(C_20,k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_20,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    k2_xboole_0(k1_zfmisc_1('#skF_5'),k1_zfmisc_1('#skF_6')) = k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    k2_xboole_0(k1_zfmisc_1('#skF_5'),k1_zfmisc_1('#skF_6')) = k1_zfmisc_1(k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_417,plain,(
    ! [D_64,B_65,A_66] :
      ( r2_hidden(D_64,B_65)
      | r2_hidden(D_64,A_66)
      | ~ r2_hidden(D_64,k2_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2454,plain,(
    ! [D_215] :
      ( r2_hidden(D_215,k1_zfmisc_1('#skF_6'))
      | r2_hidden(D_215,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_215,k1_zfmisc_1(k2_xboole_0('#skF_6','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_417])).

tff(c_4923,plain,(
    ! [C_304] :
      ( r2_hidden(C_304,k1_zfmisc_1('#skF_6'))
      | r2_hidden(C_304,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski(C_304,k2_xboole_0('#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38,c_2454])).

tff(c_36,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4954,plain,(
    ! [C_305] :
      ( r1_tarski(C_305,'#skF_5')
      | r2_hidden(C_305,k1_zfmisc_1('#skF_6'))
      | ~ r1_tarski(C_305,k2_xboole_0('#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4923,c_36])).

tff(c_4985,plain,(
    ! [C_306] :
      ( r1_tarski(C_306,'#skF_6')
      | r1_tarski(C_306,'#skF_5')
      | ~ r1_tarski(C_306,k2_xboole_0('#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4954,c_36])).

tff(c_5042,plain,
    ( r1_tarski(k2_xboole_0('#skF_6','#skF_5'),'#skF_6')
    | r1_tarski(k2_xboole_0('#skF_6','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_4985])).

tff(c_5088,plain,(
    r1_tarski(k2_xboole_0('#skF_6','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5042])).

tff(c_34,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(k2_xboole_0(A_13,B_14),C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5114,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_5088,c_34])).

tff(c_5133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_5114])).

tff(c_5134,plain,(
    r1_tarski(k2_xboole_0('#skF_6','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5042])).

tff(c_119,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(A_32,C_33)
      | ~ r1_tarski(k2_xboole_0(A_32,B_34),C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,(
    ! [B_2,C_33,A_1] :
      ( r1_tarski(B_2,C_33)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_5156,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_5134,c_128])).

tff(c_5175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:45:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.67/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.67/2.38  
% 6.67/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.67/2.38  %$ r3_xboole_0 > r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 6.67/2.38  
% 6.67/2.38  %Foreground sorts:
% 6.67/2.38  
% 6.67/2.38  
% 6.67/2.38  %Background operators:
% 6.67/2.38  
% 6.67/2.38  
% 6.67/2.38  %Foreground operators:
% 6.67/2.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.67/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.67/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.67/2.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.67/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.67/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.67/2.38  tff('#skF_6', type, '#skF_6': $i).
% 6.67/2.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.67/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.67/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.67/2.38  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 6.67/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.67/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.67/2.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.67/2.38  
% 6.67/2.40  tff(f_48, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_xboole_0)).
% 6.67/2.40  tff(f_64, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)) = k1_zfmisc_1(k2_xboole_0(A, B))) => r3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_zfmisc_1)).
% 6.67/2.40  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.67/2.40  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.67/2.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.67/2.40  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.67/2.40  tff(f_52, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.67/2.40  tff(c_54, plain, (![A_22, B_23]: (~r1_tarski(A_22, B_23) | r3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.67/2.40  tff(c_48, plain, (~r3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.67/2.40  tff(c_58, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_48])).
% 6.67/2.40  tff(c_59, plain, (![B_24, A_25]: (~r1_tarski(B_24, A_25) | r3_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.67/2.40  tff(c_63, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_59, c_48])).
% 6.67/2.40  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.67/2.40  tff(c_38, plain, (![C_20, A_16]: (r2_hidden(C_20, k1_zfmisc_1(A_16)) | ~r1_tarski(C_20, A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.67/2.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.67/2.40  tff(c_50, plain, (k2_xboole_0(k1_zfmisc_1('#skF_5'), k1_zfmisc_1('#skF_6'))=k1_zfmisc_1(k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.67/2.40  tff(c_52, plain, (k2_xboole_0(k1_zfmisc_1('#skF_5'), k1_zfmisc_1('#skF_6'))=k1_zfmisc_1(k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 6.67/2.40  tff(c_417, plain, (![D_64, B_65, A_66]: (r2_hidden(D_64, B_65) | r2_hidden(D_64, A_66) | ~r2_hidden(D_64, k2_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.67/2.40  tff(c_2454, plain, (![D_215]: (r2_hidden(D_215, k1_zfmisc_1('#skF_6')) | r2_hidden(D_215, k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_215, k1_zfmisc_1(k2_xboole_0('#skF_6', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_52, c_417])).
% 6.67/2.40  tff(c_4923, plain, (![C_304]: (r2_hidden(C_304, k1_zfmisc_1('#skF_6')) | r2_hidden(C_304, k1_zfmisc_1('#skF_5')) | ~r1_tarski(C_304, k2_xboole_0('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_38, c_2454])).
% 6.67/2.40  tff(c_36, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.67/2.40  tff(c_4954, plain, (![C_305]: (r1_tarski(C_305, '#skF_5') | r2_hidden(C_305, k1_zfmisc_1('#skF_6')) | ~r1_tarski(C_305, k2_xboole_0('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_4923, c_36])).
% 6.67/2.40  tff(c_4985, plain, (![C_306]: (r1_tarski(C_306, '#skF_6') | r1_tarski(C_306, '#skF_5') | ~r1_tarski(C_306, k2_xboole_0('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_4954, c_36])).
% 6.67/2.40  tff(c_5042, plain, (r1_tarski(k2_xboole_0('#skF_6', '#skF_5'), '#skF_6') | r1_tarski(k2_xboole_0('#skF_6', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_26, c_4985])).
% 6.67/2.40  tff(c_5088, plain, (r1_tarski(k2_xboole_0('#skF_6', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_5042])).
% 6.67/2.40  tff(c_34, plain, (![A_13, C_15, B_14]: (r1_tarski(A_13, C_15) | ~r1_tarski(k2_xboole_0(A_13, B_14), C_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.67/2.40  tff(c_5114, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_5088, c_34])).
% 6.67/2.40  tff(c_5133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_5114])).
% 6.67/2.40  tff(c_5134, plain, (r1_tarski(k2_xboole_0('#skF_6', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_5042])).
% 6.67/2.40  tff(c_119, plain, (![A_32, C_33, B_34]: (r1_tarski(A_32, C_33) | ~r1_tarski(k2_xboole_0(A_32, B_34), C_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.67/2.40  tff(c_128, plain, (![B_2, C_33, A_1]: (r1_tarski(B_2, C_33) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_33))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 6.67/2.40  tff(c_5156, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_5134, c_128])).
% 6.67/2.40  tff(c_5175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_5156])).
% 6.67/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.67/2.40  
% 6.67/2.40  Inference rules
% 6.67/2.40  ----------------------
% 6.67/2.40  #Ref     : 0
% 6.67/2.40  #Sup     : 1097
% 6.67/2.40  #Fact    : 6
% 6.67/2.40  #Define  : 0
% 6.67/2.40  #Split   : 3
% 6.67/2.40  #Chain   : 0
% 6.67/2.40  #Close   : 0
% 6.67/2.40  
% 6.67/2.40  Ordering : KBO
% 6.67/2.40  
% 6.67/2.40  Simplification rules
% 6.67/2.40  ----------------------
% 6.67/2.40  #Subsume      : 56
% 6.67/2.40  #Demod        : 475
% 6.67/2.40  #Tautology    : 493
% 6.67/2.40  #SimpNegUnit  : 4
% 6.67/2.40  #BackRed      : 1
% 6.67/2.40  
% 6.67/2.40  #Partial instantiations: 0
% 6.67/2.40  #Strategies tried      : 1
% 6.67/2.40  
% 6.67/2.40  Timing (in seconds)
% 6.67/2.40  ----------------------
% 6.67/2.40  Preprocessing        : 0.30
% 6.67/2.40  Parsing              : 0.16
% 6.67/2.40  CNF conversion       : 0.02
% 6.67/2.40  Main loop            : 1.30
% 6.67/2.40  Inferencing          : 0.33
% 6.67/2.40  Reduction            : 0.54
% 6.67/2.40  Demodulation         : 0.45
% 6.67/2.40  BG Simplification    : 0.04
% 6.67/2.40  Subsumption          : 0.31
% 6.67/2.40  Abstraction          : 0.05
% 6.67/2.40  MUC search           : 0.00
% 6.67/2.40  Cooper               : 0.00
% 6.67/2.40  Total                : 1.63
% 6.67/2.40  Index Insertion      : 0.00
% 6.67/2.40  Index Deletion       : 0.00
% 6.67/2.40  Index Matching       : 0.00
% 6.67/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
