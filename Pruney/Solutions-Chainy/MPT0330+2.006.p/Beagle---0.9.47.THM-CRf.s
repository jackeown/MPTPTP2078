%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:40 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  96 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_24,plain,(
    ! [A_24,C_26,B_25] : k2_xboole_0(k2_zfmisc_1(A_24,C_26),k2_zfmisc_1(B_25,C_26)) = k2_zfmisc_1(k2_xboole_0(A_24,B_25),C_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_185,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [A_48,A_49,B_50] :
      ( r1_tarski(A_48,k2_xboole_0(A_49,B_50))
      | ~ r1_tarski(A_48,A_49) ) ),
    inference(resolution,[status(thm)],[c_16,c_185])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1186,plain,(
    ! [A_122,A_123,B_124,A_125] :
      ( r1_tarski(A_122,k2_xboole_0(A_123,B_124))
      | ~ r1_tarski(A_122,A_125)
      | ~ r1_tarski(A_125,A_123) ) ),
    inference(resolution,[status(thm)],[c_208,c_10])).

tff(c_1250,plain,(
    ! [A_126,B_127] :
      ( r1_tarski('#skF_1',k2_xboole_0(A_126,B_127))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),A_126) ) ),
    inference(resolution,[status(thm)],[c_32,c_1186])).

tff(c_1319,plain,(
    ! [B_128] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_128)) ),
    inference(resolution,[status(thm)],[c_6,c_1250])).

tff(c_1333,plain,(
    ! [B_25] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_25),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1319])).

tff(c_18,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    ! [B_36,A_37] : k3_tarski(k2_tarski(B_36,A_37)) = k2_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_78])).

tff(c_22,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_22])).

tff(c_30,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1478,plain,(
    ! [A_137,B_138] :
      ( r1_tarski('#skF_2',k2_xboole_0(A_137,B_138))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),A_137) ) ),
    inference(resolution,[status(thm)],[c_30,c_1186])).

tff(c_1547,plain,(
    ! [B_139] : r1_tarski('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),B_139)) ),
    inference(resolution,[status(thm)],[c_6,c_1478])).

tff(c_1580,plain,(
    ! [B_140] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_5',B_140),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1547])).

tff(c_1598,plain,(
    ! [B_36] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(B_36,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1580])).

tff(c_26,plain,(
    ! [C_26,A_24,B_25] : k2_xboole_0(k2_zfmisc_1(C_26,A_24),k2_zfmisc_1(C_26,B_25)) = k2_zfmisc_1(C_26,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1047,plain,(
    ! [A_113,C_114,B_115,D_116] :
      ( r1_tarski(k2_xboole_0(A_113,C_114),k2_xboole_0(B_115,D_116))
      | ~ r1_tarski(C_114,D_116)
      | ~ r1_tarski(A_113,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2540,plain,(
    ! [C_187,B_188,A_190,C_191,A_189] :
      ( r1_tarski(k2_xboole_0(A_190,C_191),k2_zfmisc_1(C_187,k2_xboole_0(A_189,B_188)))
      | ~ r1_tarski(C_191,k2_zfmisc_1(C_187,B_188))
      | ~ r1_tarski(A_190,k2_zfmisc_1(C_187,A_189)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1047])).

tff(c_28,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2569,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_2540,c_28])).

tff(c_2613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1333,c_1598,c_2569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.72  
% 4.33/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.73  %$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.33/1.73  
% 4.33/1.73  %Foreground sorts:
% 4.33/1.73  
% 4.33/1.73  
% 4.33/1.73  %Background operators:
% 4.33/1.73  
% 4.33/1.73  
% 4.33/1.73  %Foreground operators:
% 4.33/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.33/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.33/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.33/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.33/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.33/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.33/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.33/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.33/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.33/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.33/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.33/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.33/1.73  
% 4.33/1.74  tff(f_63, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.33/1.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.33/1.74  tff(f_70, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.33/1.74  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.33/1.74  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.33/1.74  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.33/1.74  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.33/1.74  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 4.33/1.74  tff(c_24, plain, (![A_24, C_26, B_25]: (k2_xboole_0(k2_zfmisc_1(A_24, C_26), k2_zfmisc_1(B_25, C_26))=k2_zfmisc_1(k2_xboole_0(A_24, B_25), C_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.33/1.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.33/1.74  tff(c_32, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.33/1.74  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.33/1.74  tff(c_185, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/1.74  tff(c_208, plain, (![A_48, A_49, B_50]: (r1_tarski(A_48, k2_xboole_0(A_49, B_50)) | ~r1_tarski(A_48, A_49))), inference(resolution, [status(thm)], [c_16, c_185])).
% 4.33/1.74  tff(c_10, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/1.74  tff(c_1186, plain, (![A_122, A_123, B_124, A_125]: (r1_tarski(A_122, k2_xboole_0(A_123, B_124)) | ~r1_tarski(A_122, A_125) | ~r1_tarski(A_125, A_123))), inference(resolution, [status(thm)], [c_208, c_10])).
% 4.33/1.74  tff(c_1250, plain, (![A_126, B_127]: (r1_tarski('#skF_1', k2_xboole_0(A_126, B_127)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), A_126))), inference(resolution, [status(thm)], [c_32, c_1186])).
% 4.33/1.74  tff(c_1319, plain, (![B_128]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_128)))), inference(resolution, [status(thm)], [c_6, c_1250])).
% 4.33/1.74  tff(c_1333, plain, (![B_25]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_25), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1319])).
% 4.33/1.74  tff(c_18, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.33/1.74  tff(c_78, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.33/1.74  tff(c_93, plain, (![B_36, A_37]: (k3_tarski(k2_tarski(B_36, A_37))=k2_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_18, c_78])).
% 4.33/1.74  tff(c_22, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.33/1.74  tff(c_99, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_93, c_22])).
% 4.33/1.74  tff(c_30, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.33/1.74  tff(c_1478, plain, (![A_137, B_138]: (r1_tarski('#skF_2', k2_xboole_0(A_137, B_138)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), A_137))), inference(resolution, [status(thm)], [c_30, c_1186])).
% 4.33/1.74  tff(c_1547, plain, (![B_139]: (r1_tarski('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), B_139)))), inference(resolution, [status(thm)], [c_6, c_1478])).
% 4.33/1.74  tff(c_1580, plain, (![B_140]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_5', B_140), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1547])).
% 4.33/1.74  tff(c_1598, plain, (![B_36]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(B_36, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1580])).
% 4.33/1.74  tff(c_26, plain, (![C_26, A_24, B_25]: (k2_xboole_0(k2_zfmisc_1(C_26, A_24), k2_zfmisc_1(C_26, B_25))=k2_zfmisc_1(C_26, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.33/1.74  tff(c_1047, plain, (![A_113, C_114, B_115, D_116]: (r1_tarski(k2_xboole_0(A_113, C_114), k2_xboole_0(B_115, D_116)) | ~r1_tarski(C_114, D_116) | ~r1_tarski(A_113, B_115))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.33/1.74  tff(c_2540, plain, (![C_187, B_188, A_190, C_191, A_189]: (r1_tarski(k2_xboole_0(A_190, C_191), k2_zfmisc_1(C_187, k2_xboole_0(A_189, B_188))) | ~r1_tarski(C_191, k2_zfmisc_1(C_187, B_188)) | ~r1_tarski(A_190, k2_zfmisc_1(C_187, A_189)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1047])).
% 4.33/1.74  tff(c_28, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.33/1.74  tff(c_2569, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_2540, c_28])).
% 4.33/1.74  tff(c_2613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1333, c_1598, c_2569])).
% 4.33/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.74  
% 4.33/1.74  Inference rules
% 4.33/1.74  ----------------------
% 4.33/1.74  #Ref     : 0
% 4.33/1.74  #Sup     : 683
% 4.33/1.74  #Fact    : 0
% 4.33/1.74  #Define  : 0
% 4.33/1.74  #Split   : 4
% 4.33/1.74  #Chain   : 0
% 4.33/1.74  #Close   : 0
% 4.33/1.74  
% 4.33/1.74  Ordering : KBO
% 4.33/1.74  
% 4.33/1.74  Simplification rules
% 4.33/1.74  ----------------------
% 4.33/1.74  #Subsume      : 41
% 4.33/1.74  #Demod        : 109
% 4.33/1.74  #Tautology    : 129
% 4.33/1.74  #SimpNegUnit  : 0
% 4.33/1.74  #BackRed      : 0
% 4.33/1.74  
% 4.33/1.74  #Partial instantiations: 0
% 4.33/1.74  #Strategies tried      : 1
% 4.33/1.74  
% 4.33/1.74  Timing (in seconds)
% 4.33/1.74  ----------------------
% 4.33/1.74  Preprocessing        : 0.28
% 4.33/1.74  Parsing              : 0.15
% 4.33/1.74  CNF conversion       : 0.02
% 4.33/1.74  Main loop            : 0.75
% 4.33/1.74  Inferencing          : 0.21
% 4.33/1.74  Reduction            : 0.30
% 4.33/1.74  Demodulation         : 0.24
% 4.33/1.74  BG Simplification    : 0.03
% 4.33/1.74  Subsumption          : 0.16
% 4.33/1.74  Abstraction          : 0.04
% 4.33/1.74  MUC search           : 0.00
% 4.33/1.74  Cooper               : 0.00
% 4.33/1.74  Total                : 1.05
% 4.33/1.74  Index Insertion      : 0.00
% 4.33/1.74  Index Deletion       : 0.00
% 4.33/1.74  Index Matching       : 0.00
% 4.33/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
