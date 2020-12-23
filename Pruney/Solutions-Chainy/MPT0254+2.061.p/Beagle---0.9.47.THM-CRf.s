%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:27 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 117 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   47 ( 122 expanded)
%              Number of equality atoms :   18 (  60 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_115,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,(
    ! [A_38,B_39] : r1_tarski(A_38,k2_xboole_0(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_65])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_8])).

tff(c_75,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46])).

tff(c_130,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_75])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_14])).

tff(c_176,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_169,c_8])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_184,plain,(
    ! [A_5] : r1_xboole_0(A_5,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_63])).

tff(c_207,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,A_51)
      | ~ r1_xboole_0(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_212,plain,(
    ! [A_5] : r1_xboole_0('#skF_4',A_5) ),
    inference(resolution,[status(thm)],[c_184,c_207])).

tff(c_182,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_73])).

tff(c_251,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(A_56,B_57)
      | ~ r1_xboole_0(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_254,plain,(
    ! [B_57] :
      ( ~ r2_hidden('#skF_3',B_57)
      | ~ r1_xboole_0('#skF_4',B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_251])).

tff(c_260,plain,(
    ! [B_57] : ~ r2_hidden('#skF_3',B_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_254])).

tff(c_94,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [D_19,A_14] : r2_hidden(D_19,k2_tarski(A_14,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    ! [A_44] : r2_hidden(A_44,k1_tarski(A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_18])).

tff(c_109,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_106])).

tff(c_179,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_109])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:56:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.34  
% 2.22/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.22/1.34  
% 2.22/1.34  %Foreground sorts:
% 2.22/1.34  
% 2.22/1.34  
% 2.22/1.34  %Background operators:
% 2.22/1.34  
% 2.22/1.34  
% 2.22/1.34  %Foreground operators:
% 2.22/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.34  
% 2.22/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.22/1.35  tff(f_71, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.22/1.35  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.22/1.35  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.22/1.35  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.22/1.35  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.22/1.35  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.22/1.35  tff(f_65, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.22/1.35  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.35  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.22/1.35  tff(c_115, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.35  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.35  tff(c_65, plain, (![A_38, B_39]: (r1_tarski(A_38, k2_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.35  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_65])).
% 2.22/1.35  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.35  tff(c_73, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_8])).
% 2.22/1.35  tff(c_75, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46])).
% 2.22/1.35  tff(c_130, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_115, c_75])).
% 2.22/1.35  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.35  tff(c_169, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_14])).
% 2.22/1.35  tff(c_176, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_169, c_8])).
% 2.22/1.35  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.35  tff(c_60, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.35  tff(c_63, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 2.22/1.35  tff(c_184, plain, (![A_5]: (r1_xboole_0(A_5, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_63])).
% 2.22/1.35  tff(c_207, plain, (![B_50, A_51]: (r1_xboole_0(B_50, A_51) | ~r1_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.35  tff(c_212, plain, (![A_5]: (r1_xboole_0('#skF_4', A_5))), inference(resolution, [status(thm)], [c_184, c_207])).
% 2.22/1.35  tff(c_182, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_73])).
% 2.22/1.35  tff(c_251, plain, (![A_56, B_57]: (~r2_hidden(A_56, B_57) | ~r1_xboole_0(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.35  tff(c_254, plain, (![B_57]: (~r2_hidden('#skF_3', B_57) | ~r1_xboole_0('#skF_4', B_57))), inference(superposition, [status(thm), theory('equality')], [c_182, c_251])).
% 2.22/1.35  tff(c_260, plain, (![B_57]: (~r2_hidden('#skF_3', B_57))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_254])).
% 2.22/1.35  tff(c_94, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.22/1.35  tff(c_18, plain, (![D_19, A_14]: (r2_hidden(D_19, k2_tarski(A_14, D_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.35  tff(c_106, plain, (![A_44]: (r2_hidden(A_44, k1_tarski(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_18])).
% 2.22/1.35  tff(c_109, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_106])).
% 2.22/1.35  tff(c_179, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_109])).
% 2.22/1.35  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_179])).
% 2.22/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.35  
% 2.22/1.35  Inference rules
% 2.22/1.35  ----------------------
% 2.22/1.35  #Ref     : 0
% 2.22/1.35  #Sup     : 55
% 2.22/1.35  #Fact    : 0
% 2.22/1.35  #Define  : 0
% 2.22/1.35  #Split   : 0
% 2.22/1.35  #Chain   : 0
% 2.22/1.35  #Close   : 0
% 2.22/1.35  
% 2.22/1.35  Ordering : KBO
% 2.22/1.35  
% 2.22/1.35  Simplification rules
% 2.22/1.35  ----------------------
% 2.22/1.35  #Subsume      : 0
% 2.22/1.35  #Demod        : 36
% 2.22/1.35  #Tautology    : 43
% 2.22/1.35  #SimpNegUnit  : 1
% 2.22/1.35  #BackRed      : 12
% 2.22/1.35  
% 2.22/1.35  #Partial instantiations: 0
% 2.22/1.35  #Strategies tried      : 1
% 2.22/1.35  
% 2.22/1.35  Timing (in seconds)
% 2.22/1.35  ----------------------
% 2.22/1.35  Preprocessing        : 0.35
% 2.22/1.36  Parsing              : 0.18
% 2.22/1.36  CNF conversion       : 0.03
% 2.22/1.36  Main loop            : 0.16
% 2.22/1.36  Inferencing          : 0.05
% 2.22/1.36  Reduction            : 0.06
% 2.22/1.36  Demodulation         : 0.05
% 2.22/1.36  BG Simplification    : 0.02
% 2.22/1.36  Subsumption          : 0.03
% 2.22/1.36  Abstraction          : 0.01
% 2.22/1.36  MUC search           : 0.00
% 2.22/1.36  Cooper               : 0.00
% 2.22/1.36  Total                : 0.54
% 2.22/1.36  Index Insertion      : 0.00
% 2.22/1.36  Index Deletion       : 0.00
% 2.22/1.36  Index Matching       : 0.00
% 2.22/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
