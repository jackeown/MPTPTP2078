%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:44 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   41 (  65 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 ( 100 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ~ r1_xboole_0(k3_zfmisc_1(A,B,C),k3_zfmisc_1(D,E,F))
       => ( ~ r1_xboole_0(A,D)
          & ~ r1_xboole_0(B,E)
          & ~ r1_xboole_0(C,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_8,plain,
    ( r1_xboole_0('#skF_3','#skF_6')
    | r1_xboole_0('#skF_2','#skF_5')
    | r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( ~ r1_xboole_0(A_1,B_2)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_27,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( ~ r1_xboole_0(A_11,B_12)
      | r1_xboole_0(k2_zfmisc_1(A_11,C_13),k2_zfmisc_1(B_12,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [C_39,C_42,A_43,A_40,B_41] :
      ( ~ r1_xboole_0(A_40,k2_zfmisc_1(A_43,B_41))
      | r1_xboole_0(k2_zfmisc_1(A_40,C_39),k3_zfmisc_1(A_43,B_41,C_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_27])).

tff(c_96,plain,(
    ! [A_53,C_52,B_50,A_51,C_49,B_54] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_53,B_50),k2_zfmisc_1(A_51,B_54))
      | r1_xboole_0(k3_zfmisc_1(A_53,B_50,C_52),k3_zfmisc_1(A_51,B_54,C_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_10,plain,(
    ~ r1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_114,plain,(
    ~ r1_xboole_0('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_106])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11,c_114])).

tff(c_120,plain,
    ( r1_xboole_0('#skF_2','#skF_5')
    | r1_xboole_0('#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_122,plain,(
    r1_xboole_0('#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_138,plain,(
    ! [C_58,D_59,A_60,B_61] :
      ( ~ r1_xboole_0(C_58,D_59)
      | r1_xboole_0(k2_zfmisc_1(A_60,C_58),k2_zfmisc_1(B_61,D_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    ! [B_67,A_70,C_69,C_66,A_68] :
      ( ~ r1_xboole_0(C_66,C_69)
      | r1_xboole_0(k2_zfmisc_1(A_68,C_66),k3_zfmisc_1(A_70,B_67,C_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_138])).

tff(c_180,plain,(
    ! [C_84,B_81,A_83,B_85,A_80,C_82] :
      ( ~ r1_xboole_0(C_82,C_84)
      | r1_xboole_0(k3_zfmisc_1(A_83,B_81,C_82),k3_zfmisc_1(A_80,B_85,C_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_152])).

tff(c_183,plain,(
    ~ r1_xboole_0('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_180,c_10])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_183])).

tff(c_194,plain,(
    r1_xboole_0('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_2,plain,(
    ! [C_3,D_4,A_1,B_2] :
      ( ~ r1_xboole_0(C_3,D_4)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( ~ r1_xboole_0(A_93,B_94)
      | r1_xboole_0(k2_zfmisc_1(A_93,C_95),k2_zfmisc_1(B_94,D_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [B_118,D_121,A_120,C_119,B_117] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_120,B_118),B_117)
      | r1_xboole_0(k3_zfmisc_1(A_120,B_118,C_119),k2_zfmisc_1(B_117,D_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_218])).

tff(c_280,plain,(
    ! [B_129,B_132,C_130,A_128,A_131,C_127] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_128,B_132),k2_zfmisc_1(A_131,B_129))
      | r1_xboole_0(k3_zfmisc_1(A_128,B_132,C_127),k3_zfmisc_1(A_131,B_129,C_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_264])).

tff(c_290,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_280,c_10])).

tff(c_298,plain,(
    ~ r1_xboole_0('#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_290])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:20:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  %$ r1_xboole_0 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.03/1.28  
% 2.03/1.28  %Foreground sorts:
% 2.03/1.28  
% 2.03/1.28  
% 2.03/1.28  %Background operators:
% 2.03/1.28  
% 2.03/1.28  
% 2.03/1.28  %Foreground operators:
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.28  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.28  
% 2.03/1.29  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F]: (~r1_xboole_0(k3_zfmisc_1(A, B, C), k3_zfmisc_1(D, E, F)) => ((~r1_xboole_0(A, D) & ~r1_xboole_0(B, E)) & ~r1_xboole_0(C, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_mcart_1)).
% 2.03/1.29  tff(f_31, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.03/1.29  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.03/1.29  tff(c_8, plain, (r1_xboole_0('#skF_3', '#skF_6') | r1_xboole_0('#skF_2', '#skF_5') | r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.29  tff(c_11, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(splitLeft, [status(thm)], [c_8])).
% 2.03/1.29  tff(c_4, plain, (![A_1, B_2, C_3, D_4]: (~r1_xboole_0(A_1, B_2) | r1_xboole_0(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.29  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.29  tff(c_27, plain, (![A_11, B_12, C_13, D_14]: (~r1_xboole_0(A_11, B_12) | r1_xboole_0(k2_zfmisc_1(A_11, C_13), k2_zfmisc_1(B_12, D_14)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.29  tff(c_80, plain, (![C_39, C_42, A_43, A_40, B_41]: (~r1_xboole_0(A_40, k2_zfmisc_1(A_43, B_41)) | r1_xboole_0(k2_zfmisc_1(A_40, C_39), k3_zfmisc_1(A_43, B_41, C_42)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_27])).
% 2.03/1.29  tff(c_96, plain, (![A_53, C_52, B_50, A_51, C_49, B_54]: (~r1_xboole_0(k2_zfmisc_1(A_53, B_50), k2_zfmisc_1(A_51, B_54)) | r1_xboole_0(k3_zfmisc_1(A_53, B_50, C_52), k3_zfmisc_1(A_51, B_54, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_80])).
% 2.03/1.29  tff(c_10, plain, (~r1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.29  tff(c_106, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_96, c_10])).
% 2.03/1.29  tff(c_114, plain, (~r1_xboole_0('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_4, c_106])).
% 2.03/1.29  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11, c_114])).
% 2.03/1.29  tff(c_120, plain, (r1_xboole_0('#skF_2', '#skF_5') | r1_xboole_0('#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_8])).
% 2.03/1.29  tff(c_122, plain, (r1_xboole_0('#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_120])).
% 2.03/1.29  tff(c_138, plain, (![C_58, D_59, A_60, B_61]: (~r1_xboole_0(C_58, D_59) | r1_xboole_0(k2_zfmisc_1(A_60, C_58), k2_zfmisc_1(B_61, D_59)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.29  tff(c_152, plain, (![B_67, A_70, C_69, C_66, A_68]: (~r1_xboole_0(C_66, C_69) | r1_xboole_0(k2_zfmisc_1(A_68, C_66), k3_zfmisc_1(A_70, B_67, C_69)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_138])).
% 2.03/1.29  tff(c_180, plain, (![C_84, B_81, A_83, B_85, A_80, C_82]: (~r1_xboole_0(C_82, C_84) | r1_xboole_0(k3_zfmisc_1(A_83, B_81, C_82), k3_zfmisc_1(A_80, B_85, C_84)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_152])).
% 2.03/1.29  tff(c_183, plain, (~r1_xboole_0('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_180, c_10])).
% 2.03/1.29  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_183])).
% 2.03/1.29  tff(c_194, plain, (r1_xboole_0('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_120])).
% 2.03/1.29  tff(c_2, plain, (![C_3, D_4, A_1, B_2]: (~r1_xboole_0(C_3, D_4) | r1_xboole_0(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.29  tff(c_218, plain, (![A_93, B_94, C_95, D_96]: (~r1_xboole_0(A_93, B_94) | r1_xboole_0(k2_zfmisc_1(A_93, C_95), k2_zfmisc_1(B_94, D_96)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.29  tff(c_264, plain, (![B_118, D_121, A_120, C_119, B_117]: (~r1_xboole_0(k2_zfmisc_1(A_120, B_118), B_117) | r1_xboole_0(k3_zfmisc_1(A_120, B_118, C_119), k2_zfmisc_1(B_117, D_121)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_218])).
% 2.03/1.29  tff(c_280, plain, (![B_129, B_132, C_130, A_128, A_131, C_127]: (~r1_xboole_0(k2_zfmisc_1(A_128, B_132), k2_zfmisc_1(A_131, B_129)) | r1_xboole_0(k3_zfmisc_1(A_128, B_132, C_127), k3_zfmisc_1(A_131, B_129, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_264])).
% 2.03/1.29  tff(c_290, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_280, c_10])).
% 2.03/1.29  tff(c_298, plain, (~r1_xboole_0('#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_2, c_290])).
% 2.03/1.29  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_298])).
% 2.03/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  Inference rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Ref     : 0
% 2.03/1.29  #Sup     : 72
% 2.03/1.29  #Fact    : 0
% 2.03/1.29  #Define  : 0
% 2.03/1.29  #Split   : 2
% 2.03/1.29  #Chain   : 0
% 2.03/1.29  #Close   : 0
% 2.03/1.29  
% 2.03/1.29  Ordering : KBO
% 2.03/1.29  
% 2.03/1.29  Simplification rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Subsume      : 22
% 2.03/1.29  #Demod        : 20
% 2.03/1.29  #Tautology    : 18
% 2.03/1.29  #SimpNegUnit  : 0
% 2.03/1.29  #BackRed      : 0
% 2.03/1.29  
% 2.03/1.29  #Partial instantiations: 0
% 2.03/1.29  #Strategies tried      : 1
% 2.03/1.29  
% 2.03/1.29  Timing (in seconds)
% 2.03/1.29  ----------------------
% 2.03/1.29  Preprocessing        : 0.26
% 2.03/1.29  Parsing              : 0.15
% 2.03/1.29  CNF conversion       : 0.02
% 2.03/1.29  Main loop            : 0.25
% 2.03/1.29  Inferencing          : 0.12
% 2.03/1.29  Reduction            : 0.06
% 2.03/1.29  Demodulation         : 0.04
% 2.03/1.29  BG Simplification    : 0.01
% 2.03/1.29  Subsumption          : 0.05
% 2.03/1.29  Abstraction          : 0.01
% 2.03/1.29  MUC search           : 0.00
% 2.03/1.29  Cooper               : 0.00
% 2.03/1.29  Total                : 0.55
% 2.03/1.29  Index Insertion      : 0.00
% 2.03/1.29  Index Deletion       : 0.00
% 2.03/1.29  Index Matching       : 0.00
% 2.03/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
