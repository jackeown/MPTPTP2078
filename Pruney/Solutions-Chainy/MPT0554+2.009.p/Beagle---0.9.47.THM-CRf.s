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
% DateTime   : Thu Dec  3 10:01:04 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 (  71 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_113,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(A_31,C_32)
      | ~ r1_tarski(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [A_31] :
      ( r1_tarski(A_31,'#skF_2')
      | ~ r1_tarski(A_31,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_113])).

tff(c_243,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,k2_xboole_0(B_52,C_53))
      | ~ r1_tarski(k4_xboole_0(A_51,B_52),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_613,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,k2_xboole_0(B_81,'#skF_2'))
      | ~ r1_tarski(k4_xboole_0(A_80,B_81),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_125,c_243])).

tff(c_659,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,k2_xboole_0(B_88,'#skF_2'))
      | ~ r1_tarski(A_87,k2_xboole_0(B_88,'#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_613])).

tff(c_700,plain,(
    ! [A_87] :
      ( r1_tarski(A_87,'#skF_2')
      | ~ r1_tarski(A_87,k2_xboole_0('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_659])).

tff(c_711,plain,(
    ! [A_89] :
      ( r1_tarski(A_89,'#skF_2')
      | ~ r1_tarski(A_89,k2_xboole_0('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_700])).

tff(c_749,plain,(
    r1_tarski(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_711])).

tff(c_43,plain,(
    ! [B_25,A_26] : k2_xboole_0(B_25,A_26) = k2_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    ! [A_26,B_25] : r1_tarski(A_26,k2_xboole_0(B_25,A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_18])).

tff(c_96,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [B_25,A_26] :
      ( k2_xboole_0(B_25,A_26) = A_26
      | ~ r1_tarski(k2_xboole_0(B_25,A_26),A_26) ) ),
    inference(resolution,[status(thm)],[c_58,c_96])).

tff(c_762,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_749,c_105])).

tff(c_460,plain,(
    ! [C_69,A_70,B_71] :
      ( k2_xboole_0(k9_relat_1(C_69,A_70),k9_relat_1(C_69,B_71)) = k9_relat_1(C_69,k2_xboole_0(A_70,B_71))
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_496,plain,(
    ! [C_69,A_70,B_71] :
      ( r1_tarski(k9_relat_1(C_69,A_70),k9_relat_1(C_69,k2_xboole_0(A_70,B_71)))
      | ~ v1_relat_1(C_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_18])).

tff(c_927,plain,(
    ! [C_97] :
      ( r1_tarski(k9_relat_1(C_97,'#skF_1'),k9_relat_1(C_97,'#skF_2'))
      | ~ v1_relat_1(C_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_496])).

tff(c_22,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_936,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_927,c_22])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_936])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.43  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.69/1.43  
% 2.69/1.43  %Foreground sorts:
% 2.69/1.43  
% 2.69/1.43  
% 2.69/1.43  %Background operators:
% 2.69/1.43  
% 2.69/1.43  
% 2.69/1.43  %Foreground operators:
% 2.69/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.69/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.43  
% 3.00/1.44  tff(f_62, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 3.00/1.44  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.00/1.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.00/1.44  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.00/1.44  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.00/1.44  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.00/1.44  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.00/1.44  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.00/1.44  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 3.00/1.44  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.44  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.44  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.44  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.44  tff(c_14, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.44  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.44  tff(c_113, plain, (![A_31, C_32, B_33]: (r1_tarski(A_31, C_32) | ~r1_tarski(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.44  tff(c_125, plain, (![A_31]: (r1_tarski(A_31, '#skF_2') | ~r1_tarski(A_31, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_113])).
% 3.00/1.44  tff(c_243, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, k2_xboole_0(B_52, C_53)) | ~r1_tarski(k4_xboole_0(A_51, B_52), C_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.44  tff(c_613, plain, (![A_80, B_81]: (r1_tarski(A_80, k2_xboole_0(B_81, '#skF_2')) | ~r1_tarski(k4_xboole_0(A_80, B_81), '#skF_1'))), inference(resolution, [status(thm)], [c_125, c_243])).
% 3.00/1.44  tff(c_659, plain, (![A_87, B_88]: (r1_tarski(A_87, k2_xboole_0(B_88, '#skF_2')) | ~r1_tarski(A_87, k2_xboole_0(B_88, '#skF_1')))), inference(resolution, [status(thm)], [c_14, c_613])).
% 3.00/1.44  tff(c_700, plain, (![A_87]: (r1_tarski(A_87, '#skF_2') | ~r1_tarski(A_87, k2_xboole_0('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_659])).
% 3.00/1.44  tff(c_711, plain, (![A_89]: (r1_tarski(A_89, '#skF_2') | ~r1_tarski(A_89, k2_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_700])).
% 3.00/1.44  tff(c_749, plain, (r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_10, c_711])).
% 3.00/1.44  tff(c_43, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=k2_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.44  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.44  tff(c_58, plain, (![A_26, B_25]: (r1_tarski(A_26, k2_xboole_0(B_25, A_26)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_18])).
% 3.00/1.44  tff(c_96, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.44  tff(c_105, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=A_26 | ~r1_tarski(k2_xboole_0(B_25, A_26), A_26))), inference(resolution, [status(thm)], [c_58, c_96])).
% 3.00/1.44  tff(c_762, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_749, c_105])).
% 3.00/1.44  tff(c_460, plain, (![C_69, A_70, B_71]: (k2_xboole_0(k9_relat_1(C_69, A_70), k9_relat_1(C_69, B_71))=k9_relat_1(C_69, k2_xboole_0(A_70, B_71)) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.00/1.44  tff(c_496, plain, (![C_69, A_70, B_71]: (r1_tarski(k9_relat_1(C_69, A_70), k9_relat_1(C_69, k2_xboole_0(A_70, B_71))) | ~v1_relat_1(C_69))), inference(superposition, [status(thm), theory('equality')], [c_460, c_18])).
% 3.00/1.44  tff(c_927, plain, (![C_97]: (r1_tarski(k9_relat_1(C_97, '#skF_1'), k9_relat_1(C_97, '#skF_2')) | ~v1_relat_1(C_97))), inference(superposition, [status(thm), theory('equality')], [c_762, c_496])).
% 3.00/1.44  tff(c_22, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.44  tff(c_936, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_927, c_22])).
% 3.00/1.44  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_936])).
% 3.00/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.44  
% 3.00/1.44  Inference rules
% 3.00/1.44  ----------------------
% 3.00/1.44  #Ref     : 0
% 3.00/1.44  #Sup     : 228
% 3.00/1.44  #Fact    : 0
% 3.00/1.44  #Define  : 0
% 3.00/1.44  #Split   : 1
% 3.00/1.44  #Chain   : 0
% 3.00/1.44  #Close   : 0
% 3.00/1.44  
% 3.00/1.44  Ordering : KBO
% 3.00/1.44  
% 3.00/1.44  Simplification rules
% 3.00/1.44  ----------------------
% 3.00/1.44  #Subsume      : 59
% 3.00/1.44  #Demod        : 76
% 3.00/1.44  #Tautology    : 61
% 3.00/1.44  #SimpNegUnit  : 0
% 3.00/1.44  #BackRed      : 1
% 3.00/1.44  
% 3.00/1.44  #Partial instantiations: 0
% 3.00/1.44  #Strategies tried      : 1
% 3.00/1.44  
% 3.00/1.44  Timing (in seconds)
% 3.00/1.44  ----------------------
% 3.00/1.44  Preprocessing        : 0.28
% 3.00/1.44  Parsing              : 0.15
% 3.00/1.44  CNF conversion       : 0.02
% 3.00/1.44  Main loop            : 0.40
% 3.00/1.44  Inferencing          : 0.14
% 3.00/1.44  Reduction            : 0.13
% 3.00/1.44  Demodulation         : 0.10
% 3.00/1.44  BG Simplification    : 0.02
% 3.00/1.44  Subsumption          : 0.09
% 3.00/1.44  Abstraction          : 0.02
% 3.00/1.44  MUC search           : 0.00
% 3.00/1.44  Cooper               : 0.00
% 3.00/1.44  Total                : 0.71
% 3.00/1.44  Index Insertion      : 0.00
% 3.00/1.44  Index Deletion       : 0.00
% 3.00/1.44  Index Matching       : 0.00
% 3.00/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
