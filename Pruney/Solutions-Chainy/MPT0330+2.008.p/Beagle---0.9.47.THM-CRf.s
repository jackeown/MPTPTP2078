%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:41 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  72 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_287,plain,(
    ! [C_41,A_42,B_43] : k2_xboole_0(k2_zfmisc_1(C_41,A_42),k2_zfmisc_1(C_41,B_43)) = k2_zfmisc_1(C_41,k2_xboole_0(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    k4_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_168,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(A_32,k2_xboole_0(B_33,C_34))
      | ~ r1_tarski(k4_xboole_0(A_32,B_33),C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_174,plain,(
    ! [C_34] :
      ( r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),C_34))
      | ~ r1_tarski(k1_xboole_0,C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_168])).

tff(c_185,plain,(
    ! [C_34] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),C_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_174])).

tff(c_310,plain,(
    ! [B_43] : r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_43))) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_185])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [B_28,A_29] : k3_tarski(k2_tarski(B_28,A_29)) = k2_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_14,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_14])).

tff(c_22,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    k4_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_171,plain,(
    ! [C_34] :
      ( r1_tarski('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),C_34))
      | ~ r1_tarski(k1_xboole_0,C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_168])).

tff(c_183,plain,(
    ! [C_34] : r1_tarski('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),C_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_171])).

tff(c_345,plain,(
    ! [B_45] : r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_6',B_45))) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_183])).

tff(c_356,plain,(
    ! [A_29] : r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0(A_29,'#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_345])).

tff(c_16,plain,(
    ! [A_15,C_17,B_16] : k2_xboole_0(k2_zfmisc_1(A_15,C_17),k2_zfmisc_1(B_16,C_17)) = k2_zfmisc_1(k2_xboole_0(A_15,B_16),C_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_563,plain,(
    ! [A_57,C_58,B_59,D_60] :
      ( r1_tarski(k2_xboole_0(A_57,C_58),k2_xboole_0(B_59,D_60))
      | ~ r1_tarski(C_58,D_60)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1289,plain,(
    ! [C_96,A_99,A_100,B_97,C_98] :
      ( r1_tarski(k2_xboole_0(A_100,C_98),k2_zfmisc_1(k2_xboole_0(A_99,B_97),C_96))
      | ~ r1_tarski(C_98,k2_zfmisc_1(B_97,C_96))
      | ~ r1_tarski(A_100,k2_zfmisc_1(A_99,C_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_563])).

tff(c_20,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1292,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1289,c_20])).

tff(c_1330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_356,c_1292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.18/1.51  
% 3.18/1.51  %Foreground sorts:
% 3.18/1.51  
% 3.18/1.51  
% 3.18/1.51  %Background operators:
% 3.18/1.51  
% 3.18/1.51  
% 3.18/1.51  %Foreground operators:
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.18/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.18/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.51  
% 3.18/1.53  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 3.18/1.53  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.18/1.53  tff(f_56, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 3.18/1.53  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.18/1.53  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.18/1.53  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.18/1.53  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.18/1.53  tff(f_35, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 3.18/1.53  tff(c_287, plain, (![C_41, A_42, B_43]: (k2_xboole_0(k2_zfmisc_1(C_41, A_42), k2_zfmisc_1(C_41, B_43))=k2_zfmisc_1(C_41, k2_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.53  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.53  tff(c_24, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.18/1.53  tff(c_59, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.53  tff(c_70, plain, (k4_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_59])).
% 3.18/1.53  tff(c_168, plain, (![A_32, B_33, C_34]: (r1_tarski(A_32, k2_xboole_0(B_33, C_34)) | ~r1_tarski(k4_xboole_0(A_32, B_33), C_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.53  tff(c_174, plain, (![C_34]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), C_34)) | ~r1_tarski(k1_xboole_0, C_34))), inference(superposition, [status(thm), theory('equality')], [c_70, c_168])).
% 3.18/1.53  tff(c_185, plain, (![C_34]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), C_34)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_174])).
% 3.18/1.53  tff(c_310, plain, (![B_43]: (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_43))))), inference(superposition, [status(thm), theory('equality')], [c_287, c_185])).
% 3.18/1.53  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.53  tff(c_96, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.53  tff(c_111, plain, (![B_28, A_29]: (k3_tarski(k2_tarski(B_28, A_29))=k2_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_12, c_96])).
% 3.18/1.53  tff(c_14, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.53  tff(c_117, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_111, c_14])).
% 3.18/1.53  tff(c_22, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.18/1.53  tff(c_69, plain, (k4_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_59])).
% 3.18/1.53  tff(c_171, plain, (![C_34]: (r1_tarski('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), C_34)) | ~r1_tarski(k1_xboole_0, C_34))), inference(superposition, [status(thm), theory('equality')], [c_69, c_168])).
% 3.18/1.53  tff(c_183, plain, (![C_34]: (r1_tarski('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), C_34)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_171])).
% 3.18/1.53  tff(c_345, plain, (![B_45]: (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_6', B_45))))), inference(superposition, [status(thm), theory('equality')], [c_287, c_183])).
% 3.18/1.53  tff(c_356, plain, (![A_29]: (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0(A_29, '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_117, c_345])).
% 3.18/1.53  tff(c_16, plain, (![A_15, C_17, B_16]: (k2_xboole_0(k2_zfmisc_1(A_15, C_17), k2_zfmisc_1(B_16, C_17))=k2_zfmisc_1(k2_xboole_0(A_15, B_16), C_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.53  tff(c_563, plain, (![A_57, C_58, B_59, D_60]: (r1_tarski(k2_xboole_0(A_57, C_58), k2_xboole_0(B_59, D_60)) | ~r1_tarski(C_58, D_60) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.18/1.53  tff(c_1289, plain, (![C_96, A_99, A_100, B_97, C_98]: (r1_tarski(k2_xboole_0(A_100, C_98), k2_zfmisc_1(k2_xboole_0(A_99, B_97), C_96)) | ~r1_tarski(C_98, k2_zfmisc_1(B_97, C_96)) | ~r1_tarski(A_100, k2_zfmisc_1(A_99, C_96)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_563])).
% 3.18/1.53  tff(c_20, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.18/1.53  tff(c_1292, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_1289, c_20])).
% 3.18/1.53  tff(c_1330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_310, c_356, c_1292])).
% 3.18/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.53  
% 3.18/1.53  Inference rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Ref     : 0
% 3.18/1.53  #Sup     : 310
% 3.18/1.53  #Fact    : 0
% 3.18/1.53  #Define  : 0
% 3.18/1.53  #Split   : 0
% 3.18/1.53  #Chain   : 0
% 3.18/1.53  #Close   : 0
% 3.18/1.53  
% 3.18/1.53  Ordering : KBO
% 3.18/1.53  
% 3.18/1.53  Simplification rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Subsume      : 2
% 3.18/1.53  #Demod        : 101
% 3.18/1.53  #Tautology    : 156
% 3.18/1.53  #SimpNegUnit  : 0
% 3.18/1.53  #BackRed      : 0
% 3.18/1.53  
% 3.18/1.53  #Partial instantiations: 0
% 3.18/1.53  #Strategies tried      : 1
% 3.18/1.53  
% 3.18/1.53  Timing (in seconds)
% 3.18/1.53  ----------------------
% 3.36/1.53  Preprocessing        : 0.27
% 3.36/1.53  Parsing              : 0.16
% 3.36/1.53  CNF conversion       : 0.02
% 3.36/1.53  Main loop            : 0.48
% 3.36/1.53  Inferencing          : 0.17
% 3.36/1.53  Reduction            : 0.18
% 3.36/1.53  Demodulation         : 0.14
% 3.36/1.53  BG Simplification    : 0.02
% 3.36/1.53  Subsumption          : 0.07
% 3.36/1.53  Abstraction          : 0.02
% 3.36/1.53  MUC search           : 0.00
% 3.36/1.53  Cooper               : 0.00
% 3.36/1.53  Total                : 0.78
% 3.36/1.53  Index Insertion      : 0.00
% 3.36/1.53  Index Deletion       : 0.00
% 3.36/1.53  Index Matching       : 0.00
% 3.36/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
