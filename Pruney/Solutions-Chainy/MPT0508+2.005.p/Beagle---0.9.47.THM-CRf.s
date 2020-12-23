%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:55 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 136 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k7_relat_1(B_22,A_21),B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_193,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,'#skF_4')
      | ~ r1_tarski(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_193])).

tff(c_227,plain,(
    ! [A_21] :
      ( r1_tarski(k7_relat_1('#skF_3',A_21),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_223])).

tff(c_231,plain,(
    ! [A_46] : r1_tarski(k7_relat_1('#skF_3',A_46),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_227])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_294,plain,(
    ! [A_54] : k3_xboole_0(k7_relat_1('#skF_3',A_54),'#skF_4') = k7_relat_1('#skF_3',A_54) ),
    inference(resolution,[status(thm)],[c_231,c_4])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_100,plain,(
    ! [B_34,A_35] : k1_setfam_1(k2_tarski(B_34,A_35)) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_10])).

tff(c_172,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k4_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_203,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k3_xboole_0(A_43,B_44))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_12])).

tff(c_209,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(k3_xboole_0(B_34,A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_203])).

tff(c_300,plain,(
    ! [A_54] :
      ( v1_relat_1(k7_relat_1('#skF_3',A_54))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_209])).

tff(c_321,plain,(
    ! [A_54] : v1_relat_1(k7_relat_1('#skF_3',A_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_300])).

tff(c_230,plain,(
    ! [A_21] : r1_tarski(k7_relat_1('#skF_3',A_21),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_227])).

tff(c_14,plain,(
    ! [C_16,A_14,B_15] :
      ( k7_relat_1(k7_relat_1(C_16,A_14),B_15) = k7_relat_1(C_16,A_14)
      | ~ r1_tarski(A_14,B_15)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_332,plain,(
    ! [B_58,A_59,C_60] :
      ( r1_tarski(k7_relat_1(B_58,A_59),k7_relat_1(C_60,A_59))
      | ~ r1_tarski(B_58,C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2086,plain,(
    ! [C_134,A_135,C_136,B_137] :
      ( r1_tarski(k7_relat_1(C_134,A_135),k7_relat_1(C_136,B_137))
      | ~ r1_tarski(k7_relat_1(C_134,A_135),C_136)
      | ~ v1_relat_1(C_136)
      | ~ v1_relat_1(k7_relat_1(C_134,A_135))
      | ~ r1_tarski(A_135,B_137)
      | ~ v1_relat_1(C_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_332])).

tff(c_20,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2123,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2086,c_20])).

tff(c_2164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_321,c_26,c_230,c_2123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.70  
% 4.01/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.70  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.01/1.70  
% 4.01/1.70  %Foreground sorts:
% 4.01/1.70  
% 4.01/1.70  
% 4.01/1.70  %Background operators:
% 4.01/1.70  
% 4.01/1.70  
% 4.01/1.70  %Foreground operators:
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.01/1.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.01/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.01/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.70  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.01/1.70  
% 4.01/1.71  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 4.01/1.71  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.01/1.71  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.01/1.71  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.01/1.71  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.01/1.71  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.01/1.71  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.01/1.71  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 4.01/1.71  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 4.01/1.71  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 4.01/1.71  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.01/1.71  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.01/1.71  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.01/1.71  tff(c_18, plain, (![B_22, A_21]: (r1_tarski(k7_relat_1(B_22, A_21), B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.01/1.71  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.01/1.71  tff(c_193, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.71  tff(c_223, plain, (![A_45]: (r1_tarski(A_45, '#skF_4') | ~r1_tarski(A_45, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_193])).
% 4.01/1.71  tff(c_227, plain, (![A_21]: (r1_tarski(k7_relat_1('#skF_3', A_21), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_223])).
% 4.01/1.71  tff(c_231, plain, (![A_46]: (r1_tarski(k7_relat_1('#skF_3', A_46), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_227])).
% 4.01/1.71  tff(c_4, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.01/1.71  tff(c_294, plain, (![A_54]: (k3_xboole_0(k7_relat_1('#skF_3', A_54), '#skF_4')=k7_relat_1('#skF_3', A_54))), inference(resolution, [status(thm)], [c_231, c_4])).
% 4.01/1.71  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.01/1.71  tff(c_64, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.01/1.71  tff(c_100, plain, (![B_34, A_35]: (k1_setfam_1(k2_tarski(B_34, A_35))=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 4.01/1.71  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.01/1.71  tff(c_106, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_100, c_10])).
% 4.01/1.71  tff(c_172, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.01/1.71  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k4_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.71  tff(c_203, plain, (![A_43, B_44]: (v1_relat_1(k3_xboole_0(A_43, B_44)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_172, c_12])).
% 4.01/1.71  tff(c_209, plain, (![B_34, A_35]: (v1_relat_1(k3_xboole_0(B_34, A_35)) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_106, c_203])).
% 4.01/1.71  tff(c_300, plain, (![A_54]: (v1_relat_1(k7_relat_1('#skF_3', A_54)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_294, c_209])).
% 4.01/1.71  tff(c_321, plain, (![A_54]: (v1_relat_1(k7_relat_1('#skF_3', A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_300])).
% 4.01/1.71  tff(c_230, plain, (![A_21]: (r1_tarski(k7_relat_1('#skF_3', A_21), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_227])).
% 4.01/1.71  tff(c_14, plain, (![C_16, A_14, B_15]: (k7_relat_1(k7_relat_1(C_16, A_14), B_15)=k7_relat_1(C_16, A_14) | ~r1_tarski(A_14, B_15) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.01/1.71  tff(c_332, plain, (![B_58, A_59, C_60]: (r1_tarski(k7_relat_1(B_58, A_59), k7_relat_1(C_60, A_59)) | ~r1_tarski(B_58, C_60) | ~v1_relat_1(C_60) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.01/1.71  tff(c_2086, plain, (![C_134, A_135, C_136, B_137]: (r1_tarski(k7_relat_1(C_134, A_135), k7_relat_1(C_136, B_137)) | ~r1_tarski(k7_relat_1(C_134, A_135), C_136) | ~v1_relat_1(C_136) | ~v1_relat_1(k7_relat_1(C_134, A_135)) | ~r1_tarski(A_135, B_137) | ~v1_relat_1(C_134))), inference(superposition, [status(thm), theory('equality')], [c_14, c_332])).
% 4.01/1.71  tff(c_20, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.01/1.71  tff(c_2123, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2086, c_20])).
% 4.01/1.71  tff(c_2164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_321, c_26, c_230, c_2123])).
% 4.01/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.71  
% 4.01/1.71  Inference rules
% 4.01/1.71  ----------------------
% 4.01/1.71  #Ref     : 0
% 4.01/1.71  #Sup     : 534
% 4.01/1.71  #Fact    : 0
% 4.01/1.71  #Define  : 0
% 4.01/1.71  #Split   : 5
% 4.01/1.71  #Chain   : 0
% 4.01/1.71  #Close   : 0
% 4.01/1.71  
% 4.01/1.71  Ordering : KBO
% 4.01/1.71  
% 4.01/1.71  Simplification rules
% 4.01/1.71  ----------------------
% 4.01/1.71  #Subsume      : 67
% 4.01/1.71  #Demod        : 334
% 4.01/1.71  #Tautology    : 207
% 4.01/1.71  #SimpNegUnit  : 1
% 4.01/1.71  #BackRed      : 0
% 4.01/1.71  
% 4.01/1.71  #Partial instantiations: 0
% 4.01/1.71  #Strategies tried      : 1
% 4.01/1.71  
% 4.01/1.71  Timing (in seconds)
% 4.01/1.71  ----------------------
% 4.01/1.72  Preprocessing        : 0.28
% 4.01/1.72  Parsing              : 0.16
% 4.01/1.72  CNF conversion       : 0.02
% 4.01/1.72  Main loop            : 0.66
% 4.01/1.72  Inferencing          : 0.23
% 4.01/1.72  Reduction            : 0.24
% 4.01/1.72  Demodulation         : 0.18
% 4.01/1.72  BG Simplification    : 0.03
% 4.01/1.72  Subsumption          : 0.12
% 4.01/1.72  Abstraction          : 0.03
% 4.01/1.72  MUC search           : 0.00
% 4.01/1.72  Cooper               : 0.00
% 4.01/1.72  Total                : 0.97
% 4.01/1.72  Index Insertion      : 0.00
% 4.01/1.72  Index Deletion       : 0.00
% 4.01/1.72  Index Matching       : 0.00
% 4.01/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
