%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:55 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 224 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 526 expanded)
%              Number of equality atoms :   59 ( 434 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) != k1_xboole_0
       => ! [C] :
            ( m1_subset_1(C,k2_zfmisc_1(A,B))
           => ( C != k1_mcart_1(C)
              & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(c_14,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_59,plain,(
    ! [C_21,A_22,B_23] :
      ( k4_tarski(k1_mcart_1(C_21),k2_mcart_1(C_21)) = C_21
      | ~ m1_subset_1(C_21,k2_zfmisc_1(A_22,B_23))
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_67,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_61])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_6])).

tff(c_18,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_75])).

tff(c_105,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_107,plain,(
    k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_10,plain,(
    ! [B_6,C_7] : k1_mcart_1(k4_tarski(B_6,C_7)) != k4_tarski(B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    k4_tarski('#skF_3',k2_mcart_1('#skF_3')) != k1_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_10])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_41,c_111])).

tff(c_120,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_4])).

tff(c_127,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_18])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_127])).

tff(c_143,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_162,plain,(
    ! [C_33,A_34,B_35] :
      ( k4_tarski(k1_mcart_1(C_33),k2_mcart_1(C_33)) = C_33
      | ~ m1_subset_1(C_33,k2_zfmisc_1(A_34,B_35))
      | k1_xboole_0 = B_35
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_164,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_162])).

tff(c_170,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_164])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_176,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_6])).

tff(c_178,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_18])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_178])).

tff(c_208,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_210,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_8,plain,(
    ! [B_6,C_7] : k2_mcart_1(k4_tarski(B_6,C_7)) != k4_tarski(B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_217,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') != k2_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_8])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_143,c_217])).

tff(c_224,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_230,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_224,c_4])).

tff(c_231,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_18])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.18  %$ m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.63/1.18  
% 1.63/1.18  %Foreground sorts:
% 1.63/1.18  
% 1.63/1.18  
% 1.63/1.18  %Background operators:
% 1.63/1.18  
% 1.63/1.18  
% 1.63/1.18  %Foreground operators:
% 1.63/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.63/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.63/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.63/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.18  
% 1.89/1.19  tff(f_66, negated_conjecture, ~(![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_mcart_1)).
% 1.89/1.19  tff(f_53, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 1.89/1.19  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.89/1.19  tff(f_40, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.89/1.19  tff(c_14, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.19  tff(c_41, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_14])).
% 1.89/1.19  tff(c_16, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.19  tff(c_59, plain, (![C_21, A_22, B_23]: (k4_tarski(k1_mcart_1(C_21), k2_mcart_1(C_21))=C_21 | ~m1_subset_1(C_21, k2_zfmisc_1(A_22, B_23)) | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.19  tff(c_61, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_59])).
% 1.89/1.19  tff(c_67, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_61])).
% 1.89/1.19  tff(c_70, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_67])).
% 1.89/1.19  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.19  tff(c_73, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_6])).
% 1.89/1.19  tff(c_18, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.19  tff(c_75, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18])).
% 1.89/1.19  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_75])).
% 1.89/1.19  tff(c_105, plain, (k1_xboole_0='#skF_2' | k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_67])).
% 1.89/1.19  tff(c_107, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3'), inference(splitLeft, [status(thm)], [c_105])).
% 1.89/1.19  tff(c_10, plain, (![B_6, C_7]: (k1_mcart_1(k4_tarski(B_6, C_7))!=k4_tarski(B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.89/1.19  tff(c_111, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))!=k1_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_107, c_10])).
% 1.89/1.19  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_41, c_111])).
% 1.89/1.19  tff(c_120, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_105])).
% 1.89/1.19  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.19  tff(c_126, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_4])).
% 1.89/1.19  tff(c_127, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_18])).
% 1.89/1.19  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_127])).
% 1.89/1.19  tff(c_143, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 1.89/1.19  tff(c_162, plain, (![C_33, A_34, B_35]: (k4_tarski(k1_mcart_1(C_33), k2_mcart_1(C_33))=C_33 | ~m1_subset_1(C_33, k2_zfmisc_1(A_34, B_35)) | k1_xboole_0=B_35 | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.19  tff(c_164, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_162])).
% 1.89/1.19  tff(c_170, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_164])).
% 1.89/1.19  tff(c_173, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_170])).
% 1.89/1.19  tff(c_176, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_6])).
% 1.89/1.19  tff(c_178, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_18])).
% 1.89/1.19  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_178])).
% 1.89/1.19  tff(c_208, plain, (k1_xboole_0='#skF_2' | k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_170])).
% 1.89/1.19  tff(c_210, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_208])).
% 1.89/1.19  tff(c_8, plain, (![B_6, C_7]: (k2_mcart_1(k4_tarski(B_6, C_7))!=k4_tarski(B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.89/1.19  tff(c_217, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')!=k2_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_210, c_8])).
% 1.89/1.19  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_143, c_217])).
% 1.89/1.19  tff(c_224, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_208])).
% 1.89/1.19  tff(c_230, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_224, c_4])).
% 1.89/1.19  tff(c_231, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_18])).
% 1.89/1.19  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_231])).
% 1.89/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  Inference rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Ref     : 0
% 1.89/1.19  #Sup     : 52
% 1.89/1.19  #Fact    : 0
% 1.89/1.19  #Define  : 0
% 1.89/1.19  #Split   : 5
% 1.89/1.19  #Chain   : 0
% 1.89/1.19  #Close   : 0
% 1.89/1.19  
% 1.89/1.19  Ordering : KBO
% 1.89/1.19  
% 1.89/1.19  Simplification rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Subsume      : 1
% 1.89/1.19  #Demod        : 57
% 1.89/1.19  #Tautology    : 44
% 1.89/1.19  #SimpNegUnit  : 0
% 1.89/1.19  #BackRed      : 28
% 1.89/1.19  
% 1.89/1.19  #Partial instantiations: 0
% 1.89/1.19  #Strategies tried      : 1
% 1.89/1.19  
% 1.89/1.19  Timing (in seconds)
% 1.89/1.19  ----------------------
% 1.89/1.19  Preprocessing        : 0.26
% 1.89/1.19  Parsing              : 0.15
% 1.89/1.19  CNF conversion       : 0.02
% 1.89/1.19  Main loop            : 0.16
% 1.89/1.19  Inferencing          : 0.05
% 1.89/1.19  Reduction            : 0.05
% 1.89/1.19  Demodulation         : 0.03
% 1.89/1.19  BG Simplification    : 0.01
% 1.89/1.19  Subsumption          : 0.03
% 1.89/1.19  Abstraction          : 0.01
% 1.89/1.19  MUC search           : 0.00
% 1.89/1.19  Cooper               : 0.00
% 1.89/1.19  Total                : 0.45
% 1.89/1.19  Index Insertion      : 0.00
% 1.89/1.19  Index Deletion       : 0.00
% 1.89/1.19  Index Matching       : 0.00
% 1.89/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
