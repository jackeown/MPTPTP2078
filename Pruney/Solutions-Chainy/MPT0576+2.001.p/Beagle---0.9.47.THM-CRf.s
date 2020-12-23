%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:54 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 101 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k10_relat_1(C,A),k10_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [B_19,A_18,C_21] :
      ( r1_tarski(k10_relat_1(B_19,A_18),k10_relat_1(C_21,A_18))
      | ~ r1_tarski(B_19,C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_273,plain,(
    ! [A_42,B_43] : k2_xboole_0(A_42,k2_xboole_0(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_318,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_273])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_83])).

tff(c_226,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(k2_xboole_0(A_39,C_40),k2_xboole_0(B_41,C_40))
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_748,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k2_xboole_0(A_63,B_64),B_64)
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_226])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_769,plain,(
    ! [A_63,B_64] :
      ( k2_xboole_0(k2_xboole_0(A_63,B_64),B_64) = B_64
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_748,c_12])).

tff(c_821,plain,(
    ! [B_65,A_66] :
      ( k2_xboole_0(B_65,A_66) = B_65
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_2,c_769])).

tff(c_887,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_821])).

tff(c_952,plain,(
    ! [C_67,A_68,B_69] :
      ( k2_xboole_0(k10_relat_1(C_67,A_68),k10_relat_1(C_67,B_69)) = k10_relat_1(C_67,k2_xboole_0(A_68,B_69))
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6749,plain,(
    ! [A_146,C_147,A_148,B_149] :
      ( r1_tarski(A_146,k10_relat_1(C_147,k2_xboole_0(A_148,B_149)))
      | ~ r1_tarski(A_146,k10_relat_1(C_147,B_149))
      | ~ v1_relat_1(C_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_10])).

tff(c_7087,plain,(
    ! [A_153,C_154] :
      ( r1_tarski(A_153,k10_relat_1(C_154,'#skF_2'))
      | ~ r1_tarski(A_153,k10_relat_1(C_154,'#skF_1'))
      | ~ v1_relat_1(C_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_6749])).

tff(c_22,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7124,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7087,c_22])).

tff(c_7137,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7124])).

tff(c_7140,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_7137])).

tff(c_7144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_7140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.31  
% 5.98/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.31  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.98/2.31  
% 5.98/2.31  %Foreground sorts:
% 5.98/2.31  
% 5.98/2.31  
% 5.98/2.31  %Background operators:
% 5.98/2.31  
% 5.98/2.31  
% 5.98/2.31  %Foreground operators:
% 5.98/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.31  tff('#skF_2', type, '#skF_2': $i).
% 5.98/2.31  tff('#skF_3', type, '#skF_3': $i).
% 5.98/2.31  tff('#skF_1', type, '#skF_1': $i).
% 5.98/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.98/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.98/2.31  tff('#skF_4', type, '#skF_4': $i).
% 5.98/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.98/2.31  
% 5.98/2.33  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k10_relat_1(C, A), k10_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t180_relat_1)).
% 5.98/2.33  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 5.98/2.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.98/2.33  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.98/2.33  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.98/2.33  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.98/2.33  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 5.98/2.33  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 5.98/2.33  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.98/2.33  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.98/2.33  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.98/2.33  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.98/2.33  tff(c_20, plain, (![B_19, A_18, C_21]: (r1_tarski(k10_relat_1(B_19, A_18), k10_relat_1(C_21, A_18)) | ~r1_tarski(B_19, C_21) | ~v1_relat_1(C_21) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.98/2.33  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.98/2.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.98/2.33  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.98/2.33  tff(c_83, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.98/2.33  tff(c_273, plain, (![A_42, B_43]: (k2_xboole_0(A_42, k2_xboole_0(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(resolution, [status(thm)], [c_14, c_83])).
% 5.98/2.33  tff(c_318, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_273])).
% 5.98/2.33  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.98/2.33  tff(c_101, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_83])).
% 5.98/2.33  tff(c_226, plain, (![A_39, C_40, B_41]: (r1_tarski(k2_xboole_0(A_39, C_40), k2_xboole_0(B_41, C_40)) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.33  tff(c_748, plain, (![A_63, B_64]: (r1_tarski(k2_xboole_0(A_63, B_64), B_64) | ~r1_tarski(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_101, c_226])).
% 5.98/2.33  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.98/2.33  tff(c_769, plain, (![A_63, B_64]: (k2_xboole_0(k2_xboole_0(A_63, B_64), B_64)=B_64 | ~r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_748, c_12])).
% 5.98/2.33  tff(c_821, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=B_65 | ~r1_tarski(A_66, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_2, c_769])).
% 5.98/2.33  tff(c_887, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_24, c_821])).
% 5.98/2.33  tff(c_952, plain, (![C_67, A_68, B_69]: (k2_xboole_0(k10_relat_1(C_67, A_68), k10_relat_1(C_67, B_69))=k10_relat_1(C_67, k2_xboole_0(A_68, B_69)) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.98/2.33  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.98/2.33  tff(c_6749, plain, (![A_146, C_147, A_148, B_149]: (r1_tarski(A_146, k10_relat_1(C_147, k2_xboole_0(A_148, B_149))) | ~r1_tarski(A_146, k10_relat_1(C_147, B_149)) | ~v1_relat_1(C_147))), inference(superposition, [status(thm), theory('equality')], [c_952, c_10])).
% 5.98/2.33  tff(c_7087, plain, (![A_153, C_154]: (r1_tarski(A_153, k10_relat_1(C_154, '#skF_2')) | ~r1_tarski(A_153, k10_relat_1(C_154, '#skF_1')) | ~v1_relat_1(C_154))), inference(superposition, [status(thm), theory('equality')], [c_887, c_6749])).
% 5.98/2.33  tff(c_22, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.98/2.33  tff(c_7124, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_7087, c_22])).
% 5.98/2.33  tff(c_7137, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7124])).
% 5.98/2.33  tff(c_7140, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_7137])).
% 5.98/2.33  tff(c_7144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_7140])).
% 5.98/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.33  
% 5.98/2.33  Inference rules
% 5.98/2.33  ----------------------
% 5.98/2.33  #Ref     : 0
% 5.98/2.33  #Sup     : 1753
% 5.98/2.33  #Fact    : 0
% 5.98/2.33  #Define  : 0
% 5.98/2.33  #Split   : 3
% 5.98/2.33  #Chain   : 0
% 5.98/2.33  #Close   : 0
% 5.98/2.33  
% 5.98/2.33  Ordering : KBO
% 5.98/2.33  
% 5.98/2.33  Simplification rules
% 5.98/2.33  ----------------------
% 5.98/2.33  #Subsume      : 595
% 5.98/2.33  #Demod        : 1341
% 5.98/2.33  #Tautology    : 603
% 5.98/2.33  #SimpNegUnit  : 4
% 5.98/2.33  #BackRed      : 0
% 5.98/2.33  
% 5.98/2.33  #Partial instantiations: 0
% 5.98/2.33  #Strategies tried      : 1
% 5.98/2.33  
% 5.98/2.33  Timing (in seconds)
% 5.98/2.33  ----------------------
% 5.98/2.33  Preprocessing        : 0.29
% 5.98/2.33  Parsing              : 0.16
% 5.98/2.33  CNF conversion       : 0.02
% 5.98/2.33  Main loop            : 1.20
% 5.98/2.33  Inferencing          : 0.33
% 5.98/2.33  Reduction            : 0.50
% 5.98/2.33  Demodulation         : 0.40
% 5.98/2.33  BG Simplification    : 0.04
% 5.98/2.33  Subsumption          : 0.28
% 5.98/2.33  Abstraction          : 0.05
% 5.98/2.33  MUC search           : 0.00
% 5.98/2.33  Cooper               : 0.00
% 5.98/2.33  Total                : 1.52
% 5.98/2.33  Index Insertion      : 0.00
% 5.98/2.33  Index Deletion       : 0.00
% 5.98/2.33  Index Matching       : 0.00
% 5.98/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
