%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:40 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  84 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_18,plain,(
    ! [A_17,C_19,B_18] : k2_xboole_0(k2_zfmisc_1(A_17,C_19),k2_zfmisc_1(B_18,C_19)) = k2_zfmisc_1(k2_xboole_0(A_17,B_18),C_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [B_28,A_29] : k3_tarski(k2_tarski(B_28,A_29)) = k2_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_16])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,C_38)
      | ~ r1_tarski(B_39,C_38)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_226,plain,(
    ! [A_45,C_46,B_47,A_48] :
      ( r1_tarski(A_45,k2_xboole_0(C_46,B_47))
      | ~ r1_tarski(A_45,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_167])).

tff(c_377,plain,(
    ! [C_57,B_58] :
      ( r1_tarski('#skF_1',k2_xboole_0(C_57,B_58))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),B_58) ) ),
    inference(resolution,[status(thm)],[c_26,c_226])).

tff(c_398,plain,(
    ! [C_59] : r1_tarski('#skF_1',k2_xboole_0(C_59,k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_6,c_377])).

tff(c_478,plain,(
    ! [A_63] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),A_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_398])).

tff(c_492,plain,(
    ! [B_18] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_18),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_478])).

tff(c_24,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_248,plain,(
    ! [C_49,B_50] :
      ( r1_tarski('#skF_2',k2_xboole_0(C_49,B_50))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),B_50) ) ),
    inference(resolution,[status(thm)],[c_24,c_226])).

tff(c_269,plain,(
    ! [C_51] : r1_tarski('#skF_2',k2_xboole_0(C_51,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_6,c_248])).

tff(c_279,plain,(
    ! [A_17] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_17,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_269])).

tff(c_20,plain,(
    ! [C_19,A_17,B_18] : k2_xboole_0(k2_zfmisc_1(C_19,A_17),k2_zfmisc_1(C_19,B_18)) = k2_zfmisc_1(C_19,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_506,plain,(
    ! [A_64,C_65,B_66,D_67] :
      ( r1_tarski(k2_xboole_0(A_64,C_65),k2_xboole_0(B_66,D_67))
      | ~ r1_tarski(C_65,D_67)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2575,plain,(
    ! [A_152,C_151,A_154,B_153,C_150] :
      ( r1_tarski(k2_xboole_0(A_154,C_151),k2_zfmisc_1(C_150,k2_xboole_0(A_152,B_153)))
      | ~ r1_tarski(C_151,k2_zfmisc_1(C_150,B_153))
      | ~ r1_tarski(A_154,k2_zfmisc_1(C_150,A_152)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_506])).

tff(c_22,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2596,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_2575,c_22])).

tff(c_2653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_279,c_2596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.87  
% 4.59/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.88  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.87/1.88  
% 4.87/1.88  %Foreground sorts:
% 4.87/1.88  
% 4.87/1.88  
% 4.87/1.88  %Background operators:
% 4.87/1.88  
% 4.87/1.88  
% 4.87/1.88  %Foreground operators:
% 4.87/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.87/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.87/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.87/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.87/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.87/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.87/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.88  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.87/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.87/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.87/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.87/1.88  
% 4.87/1.89  tff(f_55, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.87/1.89  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.87/1.89  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.87/1.89  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.87/1.89  tff(f_62, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.87/1.89  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.87/1.89  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.87/1.89  tff(f_41, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 4.87/1.89  tff(c_18, plain, (![A_17, C_19, B_18]: (k2_xboole_0(k2_zfmisc_1(A_17, C_19), k2_zfmisc_1(B_18, C_19))=k2_zfmisc_1(k2_xboole_0(A_17, B_18), C_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.87/1.89  tff(c_14, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.87/1.89  tff(c_62, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.87/1.89  tff(c_78, plain, (![B_28, A_29]: (k3_tarski(k2_tarski(B_28, A_29))=k2_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_14, c_62])).
% 4.87/1.89  tff(c_16, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.87/1.89  tff(c_84, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_78, c_16])).
% 4.87/1.89  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/1.89  tff(c_26, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.87/1.89  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.87/1.89  tff(c_167, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, C_38) | ~r1_tarski(B_39, C_38) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.87/1.89  tff(c_226, plain, (![A_45, C_46, B_47, A_48]: (r1_tarski(A_45, k2_xboole_0(C_46, B_47)) | ~r1_tarski(A_45, A_48) | ~r1_tarski(A_48, B_47))), inference(resolution, [status(thm)], [c_8, c_167])).
% 4.87/1.89  tff(c_377, plain, (![C_57, B_58]: (r1_tarski('#skF_1', k2_xboole_0(C_57, B_58)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), B_58))), inference(resolution, [status(thm)], [c_26, c_226])).
% 4.87/1.89  tff(c_398, plain, (![C_59]: (r1_tarski('#skF_1', k2_xboole_0(C_59, k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_6, c_377])).
% 4.87/1.89  tff(c_478, plain, (![A_63]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), A_63)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_398])).
% 4.87/1.89  tff(c_492, plain, (![B_18]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_18), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_478])).
% 4.87/1.89  tff(c_24, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.87/1.89  tff(c_248, plain, (![C_49, B_50]: (r1_tarski('#skF_2', k2_xboole_0(C_49, B_50)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), B_50))), inference(resolution, [status(thm)], [c_24, c_226])).
% 4.87/1.89  tff(c_269, plain, (![C_51]: (r1_tarski('#skF_2', k2_xboole_0(C_51, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_6, c_248])).
% 4.87/1.89  tff(c_279, plain, (![A_17]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_17, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_269])).
% 4.87/1.89  tff(c_20, plain, (![C_19, A_17, B_18]: (k2_xboole_0(k2_zfmisc_1(C_19, A_17), k2_zfmisc_1(C_19, B_18))=k2_zfmisc_1(C_19, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.87/1.89  tff(c_506, plain, (![A_64, C_65, B_66, D_67]: (r1_tarski(k2_xboole_0(A_64, C_65), k2_xboole_0(B_66, D_67)) | ~r1_tarski(C_65, D_67) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.87/1.89  tff(c_2575, plain, (![A_152, C_151, A_154, B_153, C_150]: (r1_tarski(k2_xboole_0(A_154, C_151), k2_zfmisc_1(C_150, k2_xboole_0(A_152, B_153))) | ~r1_tarski(C_151, k2_zfmisc_1(C_150, B_153)) | ~r1_tarski(A_154, k2_zfmisc_1(C_150, A_152)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_506])).
% 4.87/1.89  tff(c_22, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.87/1.89  tff(c_2596, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_2575, c_22])).
% 4.87/1.89  tff(c_2653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_492, c_279, c_2596])).
% 4.87/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.89  
% 4.87/1.89  Inference rules
% 4.87/1.89  ----------------------
% 4.87/1.89  #Ref     : 0
% 4.87/1.89  #Sup     : 704
% 4.87/1.89  #Fact    : 0
% 4.87/1.89  #Define  : 0
% 4.87/1.89  #Split   : 4
% 4.87/1.89  #Chain   : 0
% 4.87/1.89  #Close   : 0
% 4.87/1.89  
% 4.87/1.89  Ordering : KBO
% 4.87/1.89  
% 4.87/1.89  Simplification rules
% 4.87/1.89  ----------------------
% 4.87/1.89  #Subsume      : 171
% 4.87/1.89  #Demod        : 80
% 4.87/1.89  #Tautology    : 110
% 4.87/1.89  #SimpNegUnit  : 0
% 4.87/1.89  #BackRed      : 0
% 4.87/1.89  
% 4.87/1.89  #Partial instantiations: 0
% 4.87/1.89  #Strategies tried      : 1
% 4.87/1.89  
% 4.87/1.89  Timing (in seconds)
% 4.87/1.89  ----------------------
% 4.87/1.89  Preprocessing        : 0.30
% 4.87/1.89  Parsing              : 0.16
% 4.87/1.89  CNF conversion       : 0.02
% 4.87/1.89  Main loop            : 0.82
% 4.87/1.89  Inferencing          : 0.23
% 4.87/1.89  Reduction            : 0.32
% 4.87/1.89  Demodulation         : 0.26
% 4.87/1.89  BG Simplification    : 0.03
% 4.87/1.89  Subsumption          : 0.19
% 4.87/1.89  Abstraction          : 0.03
% 4.87/1.89  MUC search           : 0.00
% 4.87/1.89  Cooper               : 0.00
% 4.87/1.89  Total                : 1.15
% 4.87/1.89  Index Insertion      : 0.00
% 4.87/1.89  Index Deletion       : 0.00
% 4.87/1.89  Index Matching       : 0.00
% 4.87/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
