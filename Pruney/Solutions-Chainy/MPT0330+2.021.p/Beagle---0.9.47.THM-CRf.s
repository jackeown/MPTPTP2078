%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:42 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   42 (  60 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  83 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_23,C_24,B_25] : k2_xboole_0(k2_zfmisc_1(A_23,C_24),k2_zfmisc_1(B_25,C_24)) = k2_zfmisc_1(k2_xboole_0(A_23,B_25),C_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1622,plain,(
    ! [A_84,A_85,B_86,C_87] :
      ( r1_tarski(A_84,k2_zfmisc_1(k2_xboole_0(A_85,B_86),C_87))
      | ~ r1_tarski(A_84,k2_zfmisc_1(B_86,C_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_4])).

tff(c_991,plain,(
    ! [C_63,A_64,B_65] : k2_xboole_0(k2_zfmisc_1(C_63,A_64),k2_zfmisc_1(C_63,B_65)) = k2_zfmisc_1(C_63,k2_xboole_0(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1569,plain,(
    ! [A_80,C_81,A_82,B_83] :
      ( r1_tarski(A_80,k2_zfmisc_1(C_81,k2_xboole_0(A_82,B_83)))
      | ~ r1_tarski(A_80,k2_zfmisc_1(C_81,B_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_4])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(A_14,k2_xboole_0(C_15,B_16))
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_14,B_2,A_1] :
      ( r1_tarski(A_14,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_14,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_927,plain,(
    ! [A_59,A_60,B_61,C_62] :
      ( r1_tarski(A_59,k2_zfmisc_1(k2_xboole_0(A_60,B_61),C_62))
      | ~ r1_tarski(A_59,k2_zfmisc_1(A_60,C_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_53])).

tff(c_106,plain,(
    ! [C_26,A_27,B_28] : k2_xboole_0(k2_zfmisc_1(C_26,A_27),k2_zfmisc_1(C_26,B_28)) = k2_zfmisc_1(C_26,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_285,plain,(
    ! [C_34,B_35,A_36] : k2_xboole_0(k2_zfmisc_1(C_34,B_35),k2_zfmisc_1(C_34,A_36)) = k2_zfmisc_1(C_34,k2_xboole_0(A_36,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_855,plain,(
    ! [A_55,C_56,A_57,B_58] :
      ( r1_tarski(A_55,k2_zfmisc_1(C_56,k2_xboole_0(A_57,B_58)))
      | ~ r1_tarski(A_55,k2_zfmisc_1(C_56,A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_4])).

tff(c_64,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(k2_xboole_0(A_20,C_21),B_22)
      | ~ r1_tarski(C_21,B_22)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_64,c_12])).

tff(c_105,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_909,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_855,c_105])).

tff(c_930,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_927,c_909])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_930])).

tff(c_989,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1615,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_1569,c_989])).

tff(c_1628,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1622,c_1615])).

tff(c_1678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.67  
% 3.50/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.67  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.50/1.67  
% 3.50/1.67  %Foreground sorts:
% 3.50/1.67  
% 3.50/1.67  
% 3.50/1.67  %Background operators:
% 3.50/1.67  
% 3.50/1.67  
% 3.50/1.67  %Foreground operators:
% 3.50/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.50/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.67  
% 3.50/1.68  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 3.50/1.68  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 3.50/1.68  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.50/1.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.50/1.68  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.50/1.68  tff(c_14, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.68  tff(c_75, plain, (![A_23, C_24, B_25]: (k2_xboole_0(k2_zfmisc_1(A_23, C_24), k2_zfmisc_1(B_25, C_24))=k2_zfmisc_1(k2_xboole_0(A_23, B_25), C_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.50/1.68  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.68  tff(c_1622, plain, (![A_84, A_85, B_86, C_87]: (r1_tarski(A_84, k2_zfmisc_1(k2_xboole_0(A_85, B_86), C_87)) | ~r1_tarski(A_84, k2_zfmisc_1(B_86, C_87)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_4])).
% 3.50/1.68  tff(c_991, plain, (![C_63, A_64, B_65]: (k2_xboole_0(k2_zfmisc_1(C_63, A_64), k2_zfmisc_1(C_63, B_65))=k2_zfmisc_1(C_63, k2_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.50/1.68  tff(c_1569, plain, (![A_80, C_81, A_82, B_83]: (r1_tarski(A_80, k2_zfmisc_1(C_81, k2_xboole_0(A_82, B_83))) | ~r1_tarski(A_80, k2_zfmisc_1(C_81, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_991, c_4])).
% 3.50/1.68  tff(c_16, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.68  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.50/1.68  tff(c_50, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, k2_xboole_0(C_15, B_16)) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.68  tff(c_53, plain, (![A_14, B_2, A_1]: (r1_tarski(A_14, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_14, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_50])).
% 3.50/1.68  tff(c_927, plain, (![A_59, A_60, B_61, C_62]: (r1_tarski(A_59, k2_zfmisc_1(k2_xboole_0(A_60, B_61), C_62)) | ~r1_tarski(A_59, k2_zfmisc_1(A_60, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_53])).
% 3.50/1.68  tff(c_106, plain, (![C_26, A_27, B_28]: (k2_xboole_0(k2_zfmisc_1(C_26, A_27), k2_zfmisc_1(C_26, B_28))=k2_zfmisc_1(C_26, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.50/1.68  tff(c_285, plain, (![C_34, B_35, A_36]: (k2_xboole_0(k2_zfmisc_1(C_34, B_35), k2_zfmisc_1(C_34, A_36))=k2_zfmisc_1(C_34, k2_xboole_0(A_36, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 3.50/1.68  tff(c_855, plain, (![A_55, C_56, A_57, B_58]: (r1_tarski(A_55, k2_zfmisc_1(C_56, k2_xboole_0(A_57, B_58))) | ~r1_tarski(A_55, k2_zfmisc_1(C_56, A_57)))), inference(superposition, [status(thm), theory('equality')], [c_285, c_4])).
% 3.50/1.68  tff(c_64, plain, (![A_20, C_21, B_22]: (r1_tarski(k2_xboole_0(A_20, C_21), B_22) | ~r1_tarski(C_21, B_22) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.50/1.68  tff(c_12, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.68  tff(c_74, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_64, c_12])).
% 3.50/1.68  tff(c_105, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_74])).
% 3.50/1.68  tff(c_909, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_855, c_105])).
% 3.50/1.68  tff(c_930, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_927, c_909])).
% 3.50/1.68  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_930])).
% 3.50/1.68  tff(c_989, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_74])).
% 3.50/1.68  tff(c_1615, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_1569, c_989])).
% 3.50/1.68  tff(c_1628, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1622, c_1615])).
% 3.50/1.68  tff(c_1678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1628])).
% 3.50/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.68  
% 3.50/1.68  Inference rules
% 3.50/1.68  ----------------------
% 3.50/1.68  #Ref     : 0
% 3.50/1.68  #Sup     : 458
% 3.50/1.68  #Fact    : 0
% 3.50/1.68  #Define  : 0
% 3.50/1.68  #Split   : 1
% 3.50/1.68  #Chain   : 0
% 3.50/1.68  #Close   : 0
% 3.50/1.68  
% 3.50/1.68  Ordering : KBO
% 3.50/1.68  
% 3.50/1.68  Simplification rules
% 3.50/1.68  ----------------------
% 3.50/1.68  #Subsume      : 43
% 3.50/1.68  #Demod        : 59
% 3.50/1.68  #Tautology    : 118
% 3.50/1.68  #SimpNegUnit  : 0
% 3.50/1.68  #BackRed      : 0
% 3.50/1.68  
% 3.50/1.68  #Partial instantiations: 0
% 3.50/1.68  #Strategies tried      : 1
% 3.50/1.68  
% 3.50/1.68  Timing (in seconds)
% 3.50/1.68  ----------------------
% 3.50/1.68  Preprocessing        : 0.30
% 3.50/1.68  Parsing              : 0.16
% 3.50/1.68  CNF conversion       : 0.02
% 3.50/1.68  Main loop            : 0.58
% 3.50/1.68  Inferencing          : 0.20
% 3.50/1.68  Reduction            : 0.23
% 3.50/1.68  Demodulation         : 0.20
% 3.50/1.68  BG Simplification    : 0.03
% 3.50/1.68  Subsumption          : 0.09
% 3.50/1.68  Abstraction          : 0.03
% 3.50/1.68  MUC search           : 0.00
% 3.50/1.68  Cooper               : 0.00
% 3.50/1.68  Total                : 0.90
% 3.50/1.68  Index Insertion      : 0.00
% 3.50/1.68  Index Deletion       : 0.00
% 3.50/1.68  Index Matching       : 0.00
% 3.50/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
