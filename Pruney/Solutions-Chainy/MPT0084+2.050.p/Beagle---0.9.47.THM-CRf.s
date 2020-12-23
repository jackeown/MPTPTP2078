%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:10 EST 2020

% Result     : Theorem 15.61s
% Output     : CNFRefutation 15.61s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 103 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_28])).

tff(c_196,plain,(
    ! [A_54,B_55,C_56] : r1_tarski(k2_xboole_0(k3_xboole_0(A_54,B_55),k3_xboole_0(A_54,C_56)),k2_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_219,plain,(
    ! [A_57,B_58,C_59] : r1_tarski(k3_xboole_0(A_57,B_58),k2_xboole_0(B_58,C_59)) ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_231,plain,(
    ! [A_57] : r1_tarski(k3_xboole_0(A_57,'#skF_1'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_219])).

tff(c_87,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(A_42,k3_xboole_0(B_43,C_44))
      | ~ r1_tarski(A_42,C_44)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_xboole_0(A_42,k3_xboole_0(B_43,C_44)) = k3_xboole_0(B_43,C_44)
      | ~ r1_tarski(A_42,C_44)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_87,c_6])).

tff(c_215,plain,(
    ! [A_54] : r1_tarski(k2_xboole_0(k3_xboole_0(A_54,'#skF_1'),k3_xboole_0(A_54,'#skF_3')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_196])).

tff(c_905,plain,(
    ! [A_111,B_112,C_113,B_114] :
      ( r1_tarski(A_111,k3_xboole_0(B_112,C_113))
      | ~ r1_tarski(k2_xboole_0(A_111,B_114),C_113)
      | ~ r1_tarski(k2_xboole_0(A_111,B_114),B_112) ) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_35865,plain,(
    ! [A_1208,B_1209] :
      ( r1_tarski(k3_xboole_0(A_1208,'#skF_1'),k3_xboole_0(B_1209,'#skF_3'))
      | ~ r1_tarski(k2_xboole_0(k3_xboole_0(A_1208,'#skF_1'),k3_xboole_0(A_1208,'#skF_3')),B_1209) ) ),
    inference(resolution,[status(thm)],[c_215,c_905])).

tff(c_35889,plain,(
    ! [B_43,B_1209] :
      ( r1_tarski(k3_xboole_0(B_43,'#skF_1'),k3_xboole_0(B_1209,'#skF_3'))
      | ~ r1_tarski(k3_xboole_0(B_43,'#skF_3'),B_1209)
      | ~ r1_tarski(k3_xboole_0(B_43,'#skF_1'),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_43,'#skF_1'),B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_35865])).

tff(c_35916,plain,(
    ! [B_1210,B_1211] :
      ( r1_tarski(k3_xboole_0(B_1210,'#skF_1'),k3_xboole_0(B_1211,'#skF_3'))
      | ~ r1_tarski(k3_xboole_0(B_1210,'#skF_3'),B_1211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_231,c_35889])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(B_23,A_24)
      | ~ r1_xboole_0(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_68,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_xboole_0(A_38,C_39)
      | ~ r1_xboole_0(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    ! [A_38] :
      ( r1_xboole_0(A_38,'#skF_1')
      | ~ r1_tarski(A_38,k3_xboole_0('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_27,c_68])).

tff(c_36054,plain,(
    ! [B_1212] :
      ( r1_xboole_0(k3_xboole_0(B_1212,'#skF_1'),'#skF_1')
      | ~ r1_tarski(k3_xboole_0(B_1212,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_35916,c_73])).

tff(c_16,plain,(
    ! [A_19,B_20] :
      ( ~ r1_xboole_0(k3_xboole_0(A_19,B_20),B_20)
      | r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36065,plain,(
    ! [B_1213] :
      ( r1_xboole_0(B_1213,'#skF_1')
      | ~ r1_tarski(k3_xboole_0(B_1213,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36054,c_16])).

tff(c_36120,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_36065])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36518,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36120,c_2])).

tff(c_36523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_36518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.61/8.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.61/8.42  
% 15.61/8.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.61/8.42  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 15.61/8.42  
% 15.61/8.42  %Foreground sorts:
% 15.61/8.42  
% 15.61/8.42  
% 15.61/8.42  %Background operators:
% 15.61/8.42  
% 15.61/8.42  
% 15.61/8.42  %Foreground operators:
% 15.61/8.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.61/8.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.61/8.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.61/8.42  tff('#skF_2', type, '#skF_2': $i).
% 15.61/8.42  tff('#skF_3', type, '#skF_3': $i).
% 15.61/8.42  tff('#skF_1', type, '#skF_1': $i).
% 15.61/8.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.61/8.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.61/8.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.61/8.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.61/8.42  
% 15.61/8.44  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 15.61/8.44  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.61/8.44  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 15.61/8.44  tff(f_47, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 15.61/8.44  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 15.61/8.44  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 15.61/8.44  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 15.61/8.44  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 15.61/8.44  tff(f_59, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 15.61/8.44  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.61/8.44  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.61/8.44  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.61/8.44  tff(c_28, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.61/8.44  tff(c_36, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_20, c_28])).
% 15.61/8.44  tff(c_196, plain, (![A_54, B_55, C_56]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_54, B_55), k3_xboole_0(A_54, C_56)), k2_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.61/8.44  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.61/8.44  tff(c_219, plain, (![A_57, B_58, C_59]: (r1_tarski(k3_xboole_0(A_57, B_58), k2_xboole_0(B_58, C_59)))), inference(resolution, [status(thm)], [c_196, c_4])).
% 15.61/8.44  tff(c_231, plain, (![A_57]: (r1_tarski(k3_xboole_0(A_57, '#skF_1'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_219])).
% 15.61/8.44  tff(c_87, plain, (![A_42, B_43, C_44]: (r1_tarski(A_42, k3_xboole_0(B_43, C_44)) | ~r1_tarski(A_42, C_44) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.61/8.44  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.61/8.44  tff(c_101, plain, (![A_42, B_43, C_44]: (k2_xboole_0(A_42, k3_xboole_0(B_43, C_44))=k3_xboole_0(B_43, C_44) | ~r1_tarski(A_42, C_44) | ~r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_87, c_6])).
% 15.61/8.44  tff(c_215, plain, (![A_54]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_54, '#skF_1'), k3_xboole_0(A_54, '#skF_3')), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_196])).
% 15.61/8.44  tff(c_905, plain, (![A_111, B_112, C_113, B_114]: (r1_tarski(A_111, k3_xboole_0(B_112, C_113)) | ~r1_tarski(k2_xboole_0(A_111, B_114), C_113) | ~r1_tarski(k2_xboole_0(A_111, B_114), B_112))), inference(resolution, [status(thm)], [c_87, c_4])).
% 15.61/8.44  tff(c_35865, plain, (![A_1208, B_1209]: (r1_tarski(k3_xboole_0(A_1208, '#skF_1'), k3_xboole_0(B_1209, '#skF_3')) | ~r1_tarski(k2_xboole_0(k3_xboole_0(A_1208, '#skF_1'), k3_xboole_0(A_1208, '#skF_3')), B_1209))), inference(resolution, [status(thm)], [c_215, c_905])).
% 15.61/8.44  tff(c_35889, plain, (![B_43, B_1209]: (r1_tarski(k3_xboole_0(B_43, '#skF_1'), k3_xboole_0(B_1209, '#skF_3')) | ~r1_tarski(k3_xboole_0(B_43, '#skF_3'), B_1209) | ~r1_tarski(k3_xboole_0(B_43, '#skF_1'), '#skF_3') | ~r1_tarski(k3_xboole_0(B_43, '#skF_1'), B_43))), inference(superposition, [status(thm), theory('equality')], [c_101, c_35865])).
% 15.61/8.44  tff(c_35916, plain, (![B_1210, B_1211]: (r1_tarski(k3_xboole_0(B_1210, '#skF_1'), k3_xboole_0(B_1211, '#skF_3')) | ~r1_tarski(k3_xboole_0(B_1210, '#skF_3'), B_1211))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_231, c_35889])).
% 15.61/8.44  tff(c_18, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.61/8.44  tff(c_24, plain, (![B_23, A_24]: (r1_xboole_0(B_23, A_24) | ~r1_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.61/8.44  tff(c_27, plain, (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_18, c_24])).
% 15.61/8.44  tff(c_68, plain, (![A_38, C_39, B_40]: (r1_xboole_0(A_38, C_39) | ~r1_xboole_0(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.61/8.44  tff(c_73, plain, (![A_38]: (r1_xboole_0(A_38, '#skF_1') | ~r1_tarski(A_38, k3_xboole_0('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_27, c_68])).
% 15.61/8.44  tff(c_36054, plain, (![B_1212]: (r1_xboole_0(k3_xboole_0(B_1212, '#skF_1'), '#skF_1') | ~r1_tarski(k3_xboole_0(B_1212, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_35916, c_73])).
% 15.61/8.44  tff(c_16, plain, (![A_19, B_20]: (~r1_xboole_0(k3_xboole_0(A_19, B_20), B_20) | r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.61/8.44  tff(c_36065, plain, (![B_1213]: (r1_xboole_0(B_1213, '#skF_1') | ~r1_tarski(k3_xboole_0(B_1213, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_36054, c_16])).
% 15.61/8.44  tff(c_36120, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_8, c_36065])).
% 15.61/8.44  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.61/8.44  tff(c_36518, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36120, c_2])).
% 15.61/8.44  tff(c_36523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_36518])).
% 15.61/8.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.61/8.44  
% 15.61/8.44  Inference rules
% 15.61/8.44  ----------------------
% 15.61/8.44  #Ref     : 0
% 15.61/8.44  #Sup     : 9444
% 15.61/8.44  #Fact    : 0
% 15.61/8.44  #Define  : 0
% 15.61/8.44  #Split   : 12
% 15.61/8.44  #Chain   : 0
% 15.61/8.44  #Close   : 0
% 15.61/8.44  
% 15.61/8.44  Ordering : KBO
% 15.61/8.44  
% 15.61/8.44  Simplification rules
% 15.61/8.44  ----------------------
% 15.61/8.44  #Subsume      : 1405
% 15.61/8.44  #Demod        : 3575
% 15.61/8.44  #Tautology    : 3207
% 15.61/8.44  #SimpNegUnit  : 1
% 15.61/8.44  #BackRed      : 0
% 15.61/8.44  
% 15.61/8.44  #Partial instantiations: 0
% 15.61/8.44  #Strategies tried      : 1
% 15.61/8.44  
% 15.61/8.44  Timing (in seconds)
% 15.61/8.44  ----------------------
% 15.61/8.44  Preprocessing        : 0.26
% 15.61/8.44  Parsing              : 0.15
% 15.61/8.44  CNF conversion       : 0.02
% 15.61/8.44  Main loop            : 7.42
% 15.61/8.44  Inferencing          : 1.05
% 15.61/8.44  Reduction            : 3.45
% 15.61/8.44  Demodulation         : 2.99
% 15.61/8.44  BG Simplification    : 0.12
% 15.61/8.44  Subsumption          : 2.41
% 15.61/8.44  Abstraction          : 0.17
% 15.61/8.44  MUC search           : 0.00
% 15.61/8.44  Cooper               : 0.00
% 15.61/8.44  Total                : 7.71
% 15.61/8.44  Index Insertion      : 0.00
% 15.61/8.44  Index Deletion       : 0.00
% 15.61/8.44  Index Matching       : 0.00
% 15.61/8.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
