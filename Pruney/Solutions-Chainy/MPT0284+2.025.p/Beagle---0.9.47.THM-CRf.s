%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:30 EST 2020

% Result     : Theorem 12.06s
% Output     : CNFRefutation 12.06s
% Verified   : 
% Statistics : Number of formulae       :   54 (  79 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 121 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),k4_xboole_0(B_7,A_6)) = k5_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_61,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_18,B_37] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_18),B_37),A_18)
      | r1_tarski(k1_zfmisc_1(A_18),B_37) ) ),
    inference(resolution,[status(thm)],[c_61,c_22])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,k2_xboole_0(C_12,B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [C_22,A_18] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_55,plain,(
    ! [A_34,B_35] :
      ( ~ r2_hidden('#skF_1'(A_34,B_35),B_35)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_52,A_53] :
      ( r1_tarski(A_52,k1_zfmisc_1(A_53))
      | ~ r1_tarski('#skF_1'(A_52,k1_zfmisc_1(A_53)),A_53) ) ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_29142,plain,(
    ! [A_904,C_905,B_906] :
      ( r1_tarski(A_904,k1_zfmisc_1(k2_xboole_0(C_905,B_906)))
      | ~ r1_tarski('#skF_1'(A_904,k1_zfmisc_1(k2_xboole_0(C_905,B_906))),B_906) ) ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_29264,plain,(
    ! [A_907,C_908] : r1_tarski(k1_zfmisc_1(A_907),k1_zfmisc_1(k2_xboole_0(C_908,A_907))) ),
    inference(resolution,[status(thm)],[c_72,c_29142])).

tff(c_29354,plain,(
    ! [B_7,A_6] : r1_tarski(k1_zfmisc_1(k4_xboole_0(B_7,A_6)),k1_zfmisc_1(k5_xboole_0(A_6,B_7))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_29264])).

tff(c_100,plain,(
    ! [A_48,B_49] : k2_xboole_0(k4_xboole_0(A_48,B_49),k4_xboole_0(B_49,A_48)) = k5_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    ! [A_48,B_49] : r1_tarski(k4_xboole_0(A_48,B_49),k5_xboole_0(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_18])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_129,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(k2_xboole_0(A_54,C_55),B_56)
      | ~ r1_tarski(C_55,B_56)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(k2_xboole_0(A_13,B_14),A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_73])).

tff(c_133,plain,(
    ! [B_56,C_55] :
      ( k2_xboole_0(B_56,C_55) = B_56
      | ~ r1_tarski(C_55,B_56)
      | ~ r1_tarski(B_56,B_56) ) ),
    inference(resolution,[status(thm)],[c_129,c_78])).

tff(c_147,plain,(
    ! [B_57,C_58] :
      ( k2_xboole_0(B_57,C_58) = B_57
      | ~ r1_tarski(C_58,B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_164,plain,(
    ! [A_48,B_49] : k2_xboole_0(k5_xboole_0(A_48,B_49),k4_xboole_0(A_48,B_49)) = k5_xboole_0(A_48,B_49) ),
    inference(resolution,[status(thm)],[c_112,c_147])).

tff(c_12756,plain,(
    ! [A_444,C_445,B_446] :
      ( r1_tarski(A_444,k1_zfmisc_1(k2_xboole_0(C_445,B_446)))
      | ~ r1_tarski('#skF_1'(A_444,k1_zfmisc_1(k2_xboole_0(C_445,B_446))),B_446) ) ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_12865,plain,(
    ! [A_447,C_448] : r1_tarski(k1_zfmisc_1(A_447),k1_zfmisc_1(k2_xboole_0(C_448,A_447))) ),
    inference(resolution,[status(thm)],[c_72,c_12756])).

tff(c_12936,plain,(
    ! [A_48,B_49] : r1_tarski(k1_zfmisc_1(k4_xboole_0(A_48,B_49)),k1_zfmisc_1(k5_xboole_0(A_48,B_49))) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_12865])).

tff(c_36,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4'))),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_129,c_36])).

tff(c_213,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_13735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12936,c_213])).

tff(c_13736,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_29511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29354,c_13736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.06/4.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/4.54  
% 12.06/4.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/4.54  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 12.06/4.54  
% 12.06/4.54  %Foreground sorts:
% 12.06/4.54  
% 12.06/4.54  
% 12.06/4.54  %Background operators:
% 12.06/4.54  
% 12.06/4.54  
% 12.06/4.54  %Foreground operators:
% 12.06/4.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.06/4.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.06/4.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.06/4.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.06/4.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.06/4.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.06/4.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.06/4.54  tff('#skF_5', type, '#skF_5': $i).
% 12.06/4.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.06/4.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.06/4.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.06/4.54  tff('#skF_4', type, '#skF_4': $i).
% 12.06/4.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.06/4.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.06/4.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.06/4.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.06/4.54  
% 12.06/4.55  tff(f_34, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 12.06/4.55  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.06/4.55  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.06/4.55  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 12.06/4.55  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.06/4.55  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.06/4.55  tff(f_52, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 12.06/4.55  tff(f_64, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 12.06/4.55  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), k4_xboole_0(B_7, A_6))=k5_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.06/4.55  tff(c_61, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), A_36) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.06/4.55  tff(c_22, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.06/4.55  tff(c_72, plain, (![A_18, B_37]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_18), B_37), A_18) | r1_tarski(k1_zfmisc_1(A_18), B_37))), inference(resolution, [status(thm)], [c_61, c_22])).
% 12.06/4.55  tff(c_16, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, k2_xboole_0(C_12, B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.06/4.55  tff(c_24, plain, (![C_22, A_18]: (r2_hidden(C_22, k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.06/4.55  tff(c_55, plain, (![A_34, B_35]: (~r2_hidden('#skF_1'(A_34, B_35), B_35) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.06/4.55  tff(c_123, plain, (![A_52, A_53]: (r1_tarski(A_52, k1_zfmisc_1(A_53)) | ~r1_tarski('#skF_1'(A_52, k1_zfmisc_1(A_53)), A_53))), inference(resolution, [status(thm)], [c_24, c_55])).
% 12.06/4.55  tff(c_29142, plain, (![A_904, C_905, B_906]: (r1_tarski(A_904, k1_zfmisc_1(k2_xboole_0(C_905, B_906))) | ~r1_tarski('#skF_1'(A_904, k1_zfmisc_1(k2_xboole_0(C_905, B_906))), B_906))), inference(resolution, [status(thm)], [c_16, c_123])).
% 12.06/4.55  tff(c_29264, plain, (![A_907, C_908]: (r1_tarski(k1_zfmisc_1(A_907), k1_zfmisc_1(k2_xboole_0(C_908, A_907))))), inference(resolution, [status(thm)], [c_72, c_29142])).
% 12.06/4.55  tff(c_29354, plain, (![B_7, A_6]: (r1_tarski(k1_zfmisc_1(k4_xboole_0(B_7, A_6)), k1_zfmisc_1(k5_xboole_0(A_6, B_7))))), inference(superposition, [status(thm), theory('equality')], [c_8, c_29264])).
% 12.06/4.55  tff(c_100, plain, (![A_48, B_49]: (k2_xboole_0(k4_xboole_0(A_48, B_49), k4_xboole_0(B_49, A_48))=k5_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.06/4.55  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.06/4.55  tff(c_112, plain, (![A_48, B_49]: (r1_tarski(k4_xboole_0(A_48, B_49), k5_xboole_0(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_18])).
% 12.06/4.55  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.06/4.55  tff(c_129, plain, (![A_54, C_55, B_56]: (r1_tarski(k2_xboole_0(A_54, C_55), B_56) | ~r1_tarski(C_55, B_56) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.06/4.55  tff(c_73, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.06/4.55  tff(c_78, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(k2_xboole_0(A_13, B_14), A_13))), inference(resolution, [status(thm)], [c_18, c_73])).
% 12.06/4.55  tff(c_133, plain, (![B_56, C_55]: (k2_xboole_0(B_56, C_55)=B_56 | ~r1_tarski(C_55, B_56) | ~r1_tarski(B_56, B_56))), inference(resolution, [status(thm)], [c_129, c_78])).
% 12.06/4.55  tff(c_147, plain, (![B_57, C_58]: (k2_xboole_0(B_57, C_58)=B_57 | ~r1_tarski(C_58, B_57))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_133])).
% 12.06/4.55  tff(c_164, plain, (![A_48, B_49]: (k2_xboole_0(k5_xboole_0(A_48, B_49), k4_xboole_0(A_48, B_49))=k5_xboole_0(A_48, B_49))), inference(resolution, [status(thm)], [c_112, c_147])).
% 12.06/4.55  tff(c_12756, plain, (![A_444, C_445, B_446]: (r1_tarski(A_444, k1_zfmisc_1(k2_xboole_0(C_445, B_446))) | ~r1_tarski('#skF_1'(A_444, k1_zfmisc_1(k2_xboole_0(C_445, B_446))), B_446))), inference(resolution, [status(thm)], [c_16, c_123])).
% 12.06/4.55  tff(c_12865, plain, (![A_447, C_448]: (r1_tarski(k1_zfmisc_1(A_447), k1_zfmisc_1(k2_xboole_0(C_448, A_447))))), inference(resolution, [status(thm)], [c_72, c_12756])).
% 12.06/4.55  tff(c_12936, plain, (![A_48, B_49]: (r1_tarski(k1_zfmisc_1(k4_xboole_0(A_48, B_49)), k1_zfmisc_1(k5_xboole_0(A_48, B_49))))), inference(superposition, [status(thm), theory('equality')], [c_164, c_12865])).
% 12.06/4.55  tff(c_36, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4'))), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.06/4.55  tff(c_145, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_129, c_36])).
% 12.06/4.55  tff(c_213, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_145])).
% 12.06/4.55  tff(c_13735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12936, c_213])).
% 12.06/4.55  tff(c_13736, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_145])).
% 12.06/4.55  tff(c_29511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29354, c_13736])).
% 12.06/4.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/4.55  
% 12.06/4.55  Inference rules
% 12.06/4.55  ----------------------
% 12.06/4.55  #Ref     : 0
% 12.06/4.55  #Sup     : 7361
% 12.06/4.55  #Fact    : 0
% 12.06/4.55  #Define  : 0
% 12.06/4.55  #Split   : 2
% 12.06/4.55  #Chain   : 0
% 12.06/4.55  #Close   : 0
% 12.06/4.55  
% 12.06/4.55  Ordering : KBO
% 12.06/4.55  
% 12.06/4.55  Simplification rules
% 12.06/4.55  ----------------------
% 12.06/4.55  #Subsume      : 769
% 12.06/4.55  #Demod        : 3072
% 12.06/4.55  #Tautology    : 2786
% 12.06/4.55  #SimpNegUnit  : 0
% 12.06/4.55  #BackRed      : 2
% 12.06/4.55  
% 12.06/4.55  #Partial instantiations: 0
% 12.06/4.55  #Strategies tried      : 1
% 12.06/4.55  
% 12.06/4.55  Timing (in seconds)
% 12.06/4.55  ----------------------
% 12.06/4.56  Preprocessing        : 0.29
% 12.06/4.56  Parsing              : 0.16
% 12.06/4.56  CNF conversion       : 0.02
% 12.06/4.56  Main loop            : 3.48
% 12.06/4.56  Inferencing          : 0.79
% 12.06/4.56  Reduction            : 1.38
% 12.06/4.56  Demodulation         : 1.16
% 12.06/4.56  BG Simplification    : 0.11
% 12.06/4.56  Subsumption          : 0.95
% 12.06/4.56  Abstraction          : 0.15
% 12.06/4.56  MUC search           : 0.00
% 12.06/4.56  Cooper               : 0.00
% 12.06/4.56  Total                : 3.80
% 12.06/4.56  Index Insertion      : 0.00
% 12.06/4.56  Index Deletion       : 0.00
% 12.06/4.56  Index Matching       : 0.00
% 12.06/4.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
