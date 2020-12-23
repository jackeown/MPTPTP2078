%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:43 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  73 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_616,plain,(
    ! [A_77,C_78,B_79] : k2_xboole_0(k2_zfmisc_1(A_77,C_78),k2_zfmisc_1(B_79,C_78)) = k2_zfmisc_1(k2_xboole_0(A_77,B_79),C_78) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(k2_xboole_0(A_34,B_36),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [A_3,B_4,B_38] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_38)) ),
    inference(resolution,[status(thm)],[c_104,c_8])).

tff(c_292,plain,(
    ! [B_38] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_120])).

tff(c_638,plain,(
    ! [B_79] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_79),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_292])).

tff(c_26,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_47,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_32])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_173,plain,(
    ! [A_48,B_49,C_50] :
      ( r1_tarski(A_48,k2_xboole_0(B_49,C_50))
      | ~ r1_tarski(k4_xboole_0(A_48,B_49),C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_201,plain,(
    ! [A_51,B_52] : r1_tarski(A_51,k2_xboole_0(B_52,A_51)) ),
    inference(resolution,[status(thm)],[c_14,c_173])).

tff(c_222,plain,(
    ! [A_3,B_52,B_4] : r1_tarski(A_3,k2_xboole_0(B_52,k2_xboole_0(A_3,B_4))) ),
    inference(resolution,[status(thm)],[c_201,c_8])).

tff(c_507,plain,(
    ! [B_52] : r1_tarski('#skF_2',k2_xboole_0(B_52,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_222])).

tff(c_627,plain,(
    ! [A_77] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_77,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_507])).

tff(c_22,plain,(
    ! [C_21,A_19,B_20] : k2_xboole_0(k2_zfmisc_1(C_21,A_19),k2_zfmisc_1(C_21,B_20)) = k2_zfmisc_1(C_21,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_903,plain,(
    ! [A_87,C_88,B_89,D_90] :
      ( r1_tarski(k2_xboole_0(A_87,C_88),k2_xboole_0(B_89,D_90))
      | ~ r1_tarski(C_88,D_90)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4154,plain,(
    ! [C_215,A_218,A_216,B_217,C_219] :
      ( r1_tarski(k2_xboole_0(A_216,C_219),k2_zfmisc_1(C_215,k2_xboole_0(A_218,B_217)))
      | ~ r1_tarski(C_219,k2_zfmisc_1(C_215,B_217))
      | ~ r1_tarski(A_216,k2_zfmisc_1(C_215,A_218)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_903])).

tff(c_24,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4171,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_4154,c_24])).

tff(c_4250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_627,c_4171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.97  
% 4.88/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.97  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.88/1.97  
% 4.88/1.97  %Foreground sorts:
% 4.88/1.97  
% 4.88/1.97  
% 4.88/1.97  %Background operators:
% 4.88/1.97  
% 4.88/1.97  
% 4.88/1.97  %Foreground operators:
% 4.88/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.88/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.88/1.97  tff('#skF_5', type, '#skF_5': $i).
% 4.88/1.97  tff('#skF_6', type, '#skF_6': $i).
% 4.88/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.88/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.88/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.88/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.88/1.97  tff('#skF_4', type, '#skF_4': $i).
% 4.88/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.88/1.97  
% 4.88/1.98  tff(f_57, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.88/1.98  tff(f_64, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.88/1.98  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.88/1.98  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.88/1.98  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.88/1.98  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.88/1.98  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 4.88/1.98  tff(f_45, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 4.88/1.98  tff(c_616, plain, (![A_77, C_78, B_79]: (k2_xboole_0(k2_zfmisc_1(A_77, C_78), k2_zfmisc_1(B_79, C_78))=k2_zfmisc_1(k2_xboole_0(A_77, B_79), C_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.88/1.98  tff(c_28, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.88/1.98  tff(c_32, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.88/1.98  tff(c_45, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_32])).
% 4.88/1.98  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/1.98  tff(c_92, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(k2_xboole_0(A_34, B_36), C_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.88/1.98  tff(c_104, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(resolution, [status(thm)], [c_6, c_92])).
% 4.88/1.98  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.88/1.98  tff(c_120, plain, (![A_3, B_4, B_38]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_38)))), inference(resolution, [status(thm)], [c_104, c_8])).
% 4.88/1.98  tff(c_292, plain, (![B_38]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_38)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_120])).
% 4.88/1.98  tff(c_638, plain, (![B_79]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_79), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_616, c_292])).
% 4.88/1.98  tff(c_26, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.88/1.98  tff(c_47, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_32])).
% 4.88/1.98  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.88/1.98  tff(c_173, plain, (![A_48, B_49, C_50]: (r1_tarski(A_48, k2_xboole_0(B_49, C_50)) | ~r1_tarski(k4_xboole_0(A_48, B_49), C_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.88/1.98  tff(c_201, plain, (![A_51, B_52]: (r1_tarski(A_51, k2_xboole_0(B_52, A_51)))), inference(resolution, [status(thm)], [c_14, c_173])).
% 4.88/1.98  tff(c_222, plain, (![A_3, B_52, B_4]: (r1_tarski(A_3, k2_xboole_0(B_52, k2_xboole_0(A_3, B_4))))), inference(resolution, [status(thm)], [c_201, c_8])).
% 4.88/1.98  tff(c_507, plain, (![B_52]: (r1_tarski('#skF_2', k2_xboole_0(B_52, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_47, c_222])).
% 4.88/1.98  tff(c_627, plain, (![A_77]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_77, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_616, c_507])).
% 4.88/1.98  tff(c_22, plain, (![C_21, A_19, B_20]: (k2_xboole_0(k2_zfmisc_1(C_21, A_19), k2_zfmisc_1(C_21, B_20))=k2_zfmisc_1(C_21, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.88/1.98  tff(c_903, plain, (![A_87, C_88, B_89, D_90]: (r1_tarski(k2_xboole_0(A_87, C_88), k2_xboole_0(B_89, D_90)) | ~r1_tarski(C_88, D_90) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.88/1.98  tff(c_4154, plain, (![C_215, A_218, A_216, B_217, C_219]: (r1_tarski(k2_xboole_0(A_216, C_219), k2_zfmisc_1(C_215, k2_xboole_0(A_218, B_217))) | ~r1_tarski(C_219, k2_zfmisc_1(C_215, B_217)) | ~r1_tarski(A_216, k2_zfmisc_1(C_215, A_218)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_903])).
% 4.88/1.98  tff(c_24, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.88/1.98  tff(c_4171, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_4154, c_24])).
% 4.88/1.98  tff(c_4250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_638, c_627, c_4171])).
% 4.88/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.98  
% 4.88/1.98  Inference rules
% 4.88/1.98  ----------------------
% 4.88/1.98  #Ref     : 0
% 4.88/1.98  #Sup     : 1015
% 4.88/1.98  #Fact    : 0
% 4.88/1.98  #Define  : 0
% 4.88/1.98  #Split   : 2
% 4.88/1.98  #Chain   : 0
% 4.88/1.98  #Close   : 0
% 4.88/1.98  
% 4.88/1.98  Ordering : KBO
% 4.88/1.98  
% 4.88/1.98  Simplification rules
% 4.88/1.98  ----------------------
% 4.88/1.98  #Subsume      : 30
% 4.88/1.98  #Demod        : 383
% 4.88/1.98  #Tautology    : 377
% 4.88/1.98  #SimpNegUnit  : 0
% 4.88/1.98  #BackRed      : 0
% 4.88/1.98  
% 4.88/1.98  #Partial instantiations: 0
% 4.88/1.98  #Strategies tried      : 1
% 4.88/1.98  
% 4.88/1.98  Timing (in seconds)
% 4.88/1.98  ----------------------
% 5.22/1.98  Preprocessing        : 0.30
% 5.22/1.99  Parsing              : 0.17
% 5.22/1.99  CNF conversion       : 0.02
% 5.22/1.99  Main loop            : 0.89
% 5.22/1.99  Inferencing          : 0.28
% 5.22/1.99  Reduction            : 0.34
% 5.22/1.99  Demodulation         : 0.28
% 5.22/1.99  BG Simplification    : 0.03
% 5.22/1.99  Subsumption          : 0.18
% 5.22/1.99  Abstraction          : 0.04
% 5.22/1.99  MUC search           : 0.00
% 5.22/1.99  Cooper               : 0.00
% 5.22/1.99  Total                : 1.21
% 5.22/1.99  Index Insertion      : 0.00
% 5.22/1.99  Index Deletion       : 0.00
% 5.22/1.99  Index Matching       : 0.00
% 5.22/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
