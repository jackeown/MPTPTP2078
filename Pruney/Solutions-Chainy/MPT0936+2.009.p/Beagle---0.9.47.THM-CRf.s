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
% DateTime   : Thu Dec  3 10:10:28 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 152 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 204 expanded)
%              Number of equality atoms :   40 ( 176 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_165,plain,(
    ! [A_43,B_44,C_45] : k2_zfmisc_1(k2_tarski(A_43,B_44),k1_tarski(C_45)) = k2_tarski(k4_tarski(A_43,C_45),k4_tarski(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_196,plain,(
    ! [B_44,C_45] : k2_zfmisc_1(k2_tarski(B_44,B_44),k1_tarski(C_45)) = k1_tarski(k4_tarski(B_44,C_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_4])).

tff(c_251,plain,(
    ! [B_51,C_52] : k2_zfmisc_1(k1_tarski(B_51),k1_tarski(C_52)) = k1_tarski(k4_tarski(B_51,C_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_196])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( k1_relat_1(k2_zfmisc_1(A_11,B_12)) = A_11
      | k1_xboole_0 = B_12
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_260,plain,(
    ! [B_51,C_52] :
      ( k1_relat_1(k1_tarski(k4_tarski(B_51,C_52))) = k1_tarski(B_51)
      | k1_tarski(C_52) = k1_xboole_0
      | k1_tarski(B_51) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_20])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] : k4_tarski(k4_tarski(A_13,B_14),C_15) = k3_mcart_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_476,plain,(
    ! [B_91,C_92] :
      ( k1_relat_1(k1_tarski(k4_tarski(B_91,C_92))) = k1_tarski(B_91)
      | k1_tarski(C_92) = k1_xboole_0
      | k1_tarski(B_91) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_20])).

tff(c_2028,plain,(
    ! [A_293,B_294,C_295] :
      ( k1_relat_1(k1_tarski(k3_mcart_1(A_293,B_294,C_295))) = k1_tarski(k4_tarski(A_293,B_294))
      | k1_tarski(C_295) = k1_xboole_0
      | k1_tarski(k4_tarski(A_293,B_294)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_476])).

tff(c_24,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2034,plain,
    ( k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1')
    | k1_tarski('#skF_3') = k1_xboole_0
    | k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2028,c_24])).

tff(c_2044,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2034])).

tff(c_2048,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_2044])).

tff(c_2049,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2048])).

tff(c_26,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_4,B_5] : ~ v1_xboole_0(k2_tarski(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_2293,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2049,c_31])).

tff(c_2298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2293])).

tff(c_2299,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2048])).

tff(c_2542,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2299,c_31])).

tff(c_2547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2542])).

tff(c_2548,plain,
    ( k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2034])).

tff(c_2562,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2548])).

tff(c_2804,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2562,c_31])).

tff(c_2809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2804])).

tff(c_2810,plain,(
    k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2548])).

tff(c_3057,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2810,c_31])).

tff(c_3067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:31:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.14  
% 5.78/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.14  %$ v1_xboole_0 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.78/2.14  
% 5.78/2.14  %Foreground sorts:
% 5.78/2.14  
% 5.78/2.14  
% 5.78/2.14  %Background operators:
% 5.78/2.14  
% 5.78/2.14  
% 5.78/2.14  %Foreground operators:
% 5.78/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.78/2.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.78/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.78/2.14  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.78/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.78/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.78/2.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.78/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.78/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.78/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.78/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.78/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.78/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.78/2.14  
% 5.78/2.15  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.78/2.15  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.78/2.15  tff(f_46, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 5.78/2.15  tff(f_58, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 5.78/2.15  tff(f_60, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 5.78/2.15  tff(f_63, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 5.78/2.15  tff(f_33, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 5.78/2.15  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.78/2.15  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.78/2.15  tff(c_165, plain, (![A_43, B_44, C_45]: (k2_zfmisc_1(k2_tarski(A_43, B_44), k1_tarski(C_45))=k2_tarski(k4_tarski(A_43, C_45), k4_tarski(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.78/2.15  tff(c_196, plain, (![B_44, C_45]: (k2_zfmisc_1(k2_tarski(B_44, B_44), k1_tarski(C_45))=k1_tarski(k4_tarski(B_44, C_45)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_4])).
% 5.78/2.15  tff(c_251, plain, (![B_51, C_52]: (k2_zfmisc_1(k1_tarski(B_51), k1_tarski(C_52))=k1_tarski(k4_tarski(B_51, C_52)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_196])).
% 5.78/2.15  tff(c_20, plain, (![A_11, B_12]: (k1_relat_1(k2_zfmisc_1(A_11, B_12))=A_11 | k1_xboole_0=B_12 | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.78/2.15  tff(c_260, plain, (![B_51, C_52]: (k1_relat_1(k1_tarski(k4_tarski(B_51, C_52)))=k1_tarski(B_51) | k1_tarski(C_52)=k1_xboole_0 | k1_tarski(B_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_251, c_20])).
% 5.78/2.15  tff(c_22, plain, (![A_13, B_14, C_15]: (k4_tarski(k4_tarski(A_13, B_14), C_15)=k3_mcart_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.78/2.15  tff(c_476, plain, (![B_91, C_92]: (k1_relat_1(k1_tarski(k4_tarski(B_91, C_92)))=k1_tarski(B_91) | k1_tarski(C_92)=k1_xboole_0 | k1_tarski(B_91)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_251, c_20])).
% 5.78/2.15  tff(c_2028, plain, (![A_293, B_294, C_295]: (k1_relat_1(k1_tarski(k3_mcart_1(A_293, B_294, C_295)))=k1_tarski(k4_tarski(A_293, B_294)) | k1_tarski(C_295)=k1_xboole_0 | k1_tarski(k4_tarski(A_293, B_294))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_476])).
% 5.78/2.15  tff(c_24, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.78/2.15  tff(c_2034, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1') | k1_tarski('#skF_3')=k1_xboole_0 | k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2028, c_24])).
% 5.78/2.15  tff(c_2044, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_2034])).
% 5.78/2.15  tff(c_2048, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_260, c_2044])).
% 5.78/2.15  tff(c_2049, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2048])).
% 5.78/2.15  tff(c_26, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.78/2.15  tff(c_8, plain, (![A_4, B_5]: (~v1_xboole_0(k2_tarski(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.78/2.15  tff(c_31, plain, (![A_18]: (~v1_xboole_0(k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8])).
% 5.78/2.15  tff(c_2293, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2049, c_31])).
% 5.78/2.15  tff(c_2298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2293])).
% 5.78/2.15  tff(c_2299, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2048])).
% 5.78/2.15  tff(c_2542, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2299, c_31])).
% 5.78/2.15  tff(c_2547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2542])).
% 5.78/2.15  tff(c_2548, plain, (k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0 | k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2034])).
% 5.78/2.15  tff(c_2562, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2548])).
% 5.78/2.15  tff(c_2804, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2562, c_31])).
% 5.78/2.15  tff(c_2809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2804])).
% 5.78/2.15  tff(c_2810, plain, (k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2548])).
% 5.78/2.15  tff(c_3057, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2810, c_31])).
% 5.78/2.15  tff(c_3067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3057])).
% 5.78/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.15  
% 5.78/2.15  Inference rules
% 5.78/2.15  ----------------------
% 5.78/2.15  #Ref     : 0
% 5.78/2.15  #Sup     : 1160
% 5.78/2.15  #Fact    : 0
% 5.78/2.15  #Define  : 0
% 5.78/2.15  #Split   : 3
% 5.78/2.15  #Chain   : 0
% 5.78/2.15  #Close   : 0
% 5.78/2.15  
% 5.78/2.15  Ordering : KBO
% 5.78/2.15  
% 5.78/2.15  Simplification rules
% 5.78/2.15  ----------------------
% 5.78/2.15  #Subsume      : 242
% 5.78/2.15  #Demod        : 402
% 5.78/2.15  #Tautology    : 114
% 5.78/2.15  #SimpNegUnit  : 0
% 5.78/2.15  #BackRed      : 4
% 5.78/2.15  
% 5.78/2.15  #Partial instantiations: 0
% 5.78/2.15  #Strategies tried      : 1
% 5.78/2.15  
% 5.78/2.15  Timing (in seconds)
% 5.78/2.15  ----------------------
% 5.78/2.16  Preprocessing        : 0.29
% 5.78/2.16  Parsing              : 0.16
% 5.78/2.16  CNF conversion       : 0.02
% 5.78/2.16  Main loop            : 1.09
% 5.78/2.16  Inferencing          : 0.34
% 5.78/2.16  Reduction            : 0.42
% 5.78/2.16  Demodulation         : 0.35
% 5.78/2.16  BG Simplification    : 0.05
% 5.78/2.16  Subsumption          : 0.22
% 5.78/2.16  Abstraction          : 0.06
% 5.94/2.16  MUC search           : 0.00
% 5.94/2.16  Cooper               : 0.00
% 5.94/2.16  Total                : 1.41
% 5.94/2.16  Index Insertion      : 0.00
% 5.94/2.16  Index Deletion       : 0.00
% 5.94/2.16  Index Matching       : 0.00
% 5.94/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
