%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:26 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  62 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_21,B_22] : r1_tarski(k3_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_85,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_44,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_86,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_56])).

tff(c_114,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(k2_xboole_0(A_35,C_36),k2_xboole_0(B_37,C_36))
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [A_5,B_37] :
      ( r1_tarski(A_5,k2_xboole_0(B_37,A_5))
      | ~ r1_tarski(k1_xboole_0,B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_114])).

tff(c_128,plain,(
    ! [A_5,B_37] : r1_tarski(A_5,k2_xboole_0(B_37,A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_117])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k1_zfmisc_1(A_17),k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(k2_xboole_0(A_40,C_41),B_42)
      | ~ r1_tarski(C_41,B_42)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'),k1_zfmisc_1('#skF_2')),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_136,c_20])).

tff(c_164,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_167,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_172,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_176,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_172])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.21  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.21  
% 1.81/1.21  %Foreground sorts:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Background operators:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Foreground operators:
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.81/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.21  
% 1.81/1.22  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.81/1.22  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.81/1.22  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.81/1.22  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.81/1.22  tff(f_33, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.81/1.22  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 1.81/1.22  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.81/1.22  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.81/1.22  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.81/1.22  tff(f_54, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 1.81/1.22  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.22  tff(c_37, plain, (![A_21, B_22]: (r1_tarski(k3_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.22  tff(c_40, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_37])).
% 1.81/1.22  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.22  tff(c_73, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.22  tff(c_82, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_73])).
% 1.81/1.22  tff(c_85, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_82])).
% 1.81/1.22  tff(c_44, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.22  tff(c_56, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 1.81/1.22  tff(c_86, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_56])).
% 1.81/1.22  tff(c_114, plain, (![A_35, C_36, B_37]: (r1_tarski(k2_xboole_0(A_35, C_36), k2_xboole_0(B_37, C_36)) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.22  tff(c_117, plain, (![A_5, B_37]: (r1_tarski(A_5, k2_xboole_0(B_37, A_5)) | ~r1_tarski(k1_xboole_0, B_37))), inference(superposition, [status(thm), theory('equality')], [c_86, c_114])).
% 1.81/1.22  tff(c_128, plain, (![A_5, B_37]: (r1_tarski(A_5, k2_xboole_0(B_37, A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_117])).
% 1.81/1.22  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(k1_zfmisc_1(A_17), k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.81/1.22  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.22  tff(c_136, plain, (![A_40, C_41, B_42]: (r1_tarski(k2_xboole_0(A_40, C_41), B_42) | ~r1_tarski(C_41, B_42) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.22  tff(c_20, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'), k1_zfmisc_1('#skF_2')), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.22  tff(c_146, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_136, c_20])).
% 1.81/1.22  tff(c_164, plain, (~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_146])).
% 1.81/1.22  tff(c_167, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_164])).
% 1.81/1.22  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_167])).
% 1.81/1.22  tff(c_172, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_146])).
% 1.81/1.22  tff(c_176, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_172])).
% 1.81/1.22  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_176])).
% 1.81/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  Inference rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Ref     : 0
% 1.81/1.22  #Sup     : 35
% 1.81/1.22  #Fact    : 0
% 1.81/1.22  #Define  : 0
% 1.81/1.22  #Split   : 1
% 1.81/1.22  #Chain   : 0
% 1.81/1.22  #Close   : 0
% 1.81/1.22  
% 1.81/1.22  Ordering : KBO
% 1.81/1.22  
% 1.81/1.22  Simplification rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Subsume      : 0
% 1.81/1.22  #Demod        : 14
% 1.81/1.22  #Tautology    : 21
% 1.81/1.22  #SimpNegUnit  : 0
% 1.81/1.22  #BackRed      : 1
% 1.81/1.22  
% 1.81/1.22  #Partial instantiations: 0
% 1.81/1.22  #Strategies tried      : 1
% 1.81/1.22  
% 1.81/1.22  Timing (in seconds)
% 1.81/1.22  ----------------------
% 1.81/1.22  Preprocessing        : 0.28
% 1.81/1.22  Parsing              : 0.16
% 1.81/1.22  CNF conversion       : 0.02
% 1.81/1.22  Main loop            : 0.15
% 1.81/1.22  Inferencing          : 0.06
% 1.81/1.22  Reduction            : 0.04
% 1.81/1.22  Demodulation         : 0.03
% 1.81/1.22  BG Simplification    : 0.01
% 1.81/1.22  Subsumption          : 0.03
% 1.81/1.22  Abstraction          : 0.01
% 1.81/1.22  MUC search           : 0.00
% 1.81/1.22  Cooper               : 0.00
% 1.81/1.22  Total                : 0.46
% 1.81/1.22  Index Insertion      : 0.00
% 1.81/1.22  Index Deletion       : 0.00
% 1.81/1.22  Index Matching       : 0.00
% 1.81/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
