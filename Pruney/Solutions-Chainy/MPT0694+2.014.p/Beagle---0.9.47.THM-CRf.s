%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:54 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 5.86s
% Verified   : 
% Statistics : Number of formulae       :   50 (  82 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 113 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [C_17,A_15,B_16] :
      ( r1_tarski(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16))
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [B_28,A_29] : k1_setfam_1(k2_tarski(B_28,A_29)) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_12,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_104,plain,(
    ! [B_30,A_31] : k3_xboole_0(B_30,A_31) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_119,plain,(
    ! [B_30,A_31] : r1_tarski(k3_xboole_0(B_30,A_31),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_463,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,k9_relat_1(B_74,k1_relat_1(B_74))) = k9_relat_1(B_74,k10_relat_1(B_74,A_73))
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_783,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(k9_relat_1(B_91,k10_relat_1(B_91,A_92)),A_92)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_2])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2719,plain,(
    ! [A_198,A_199,B_200] :
      ( r1_tarski(A_198,A_199)
      | ~ r1_tarski(A_198,k9_relat_1(B_200,k10_relat_1(B_200,A_199)))
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(resolution,[status(thm)],[c_783,c_6])).

tff(c_6437,plain,(
    ! [C_334,A_335,A_336] :
      ( r1_tarski(k9_relat_1(C_334,A_335),A_336)
      | ~ v1_funct_1(C_334)
      | ~ r1_tarski(A_335,k10_relat_1(C_334,A_336))
      | ~ v1_relat_1(C_334) ) ),
    inference(resolution,[status(thm)],[c_14,c_2719])).

tff(c_179,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(A_40,k3_xboole_0(B_41,C_42))
      | ~ r1_tarski(A_40,C_42)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_152,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_18])).

tff(c_196,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_152])).

tff(c_270,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_6510,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6437,c_270])).

tff(c_6548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_119,c_20,c_6510])).

tff(c_6549,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_6882,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_6549])).

tff(c_6886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_6882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.31  
% 5.86/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.32  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.86/2.32  
% 5.86/2.32  %Foreground sorts:
% 5.86/2.32  
% 5.86/2.32  
% 5.86/2.32  %Background operators:
% 5.86/2.32  
% 5.86/2.32  
% 5.86/2.32  %Foreground operators:
% 5.86/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.86/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.86/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.86/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.86/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.86/2.32  tff('#skF_2', type, '#skF_2': $i).
% 5.86/2.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.86/2.32  tff('#skF_3', type, '#skF_3': $i).
% 5.86/2.32  tff('#skF_1', type, '#skF_1': $i).
% 5.86/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.86/2.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.86/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.86/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.86/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.86/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.86/2.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.86/2.32  
% 5.86/2.33  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 5.86/2.33  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.86/2.33  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 5.86/2.33  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.86/2.33  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.86/2.33  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 5.86/2.33  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.86/2.33  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.86/2.33  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.86/2.33  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.86/2.33  tff(c_14, plain, (![C_17, A_15, B_16]: (r1_tarski(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16)) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.86/2.33  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.86/2.33  tff(c_57, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.86/2.33  tff(c_81, plain, (![B_28, A_29]: (k1_setfam_1(k2_tarski(B_28, A_29))=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_8, c_57])).
% 5.86/2.33  tff(c_12, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.86/2.33  tff(c_104, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 5.86/2.33  tff(c_119, plain, (![B_30, A_31]: (r1_tarski(k3_xboole_0(B_30, A_31), A_31))), inference(superposition, [status(thm), theory('equality')], [c_104, c_2])).
% 5.86/2.33  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.86/2.33  tff(c_463, plain, (![A_73, B_74]: (k3_xboole_0(A_73, k9_relat_1(B_74, k1_relat_1(B_74)))=k9_relat_1(B_74, k10_relat_1(B_74, A_73)) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.86/2.33  tff(c_783, plain, (![B_91, A_92]: (r1_tarski(k9_relat_1(B_91, k10_relat_1(B_91, A_92)), A_92) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91))), inference(superposition, [status(thm), theory('equality')], [c_463, c_2])).
% 5.86/2.33  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.86/2.33  tff(c_2719, plain, (![A_198, A_199, B_200]: (r1_tarski(A_198, A_199) | ~r1_tarski(A_198, k9_relat_1(B_200, k10_relat_1(B_200, A_199))) | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(resolution, [status(thm)], [c_783, c_6])).
% 5.86/2.33  tff(c_6437, plain, (![C_334, A_335, A_336]: (r1_tarski(k9_relat_1(C_334, A_335), A_336) | ~v1_funct_1(C_334) | ~r1_tarski(A_335, k10_relat_1(C_334, A_336)) | ~v1_relat_1(C_334))), inference(resolution, [status(thm)], [c_14, c_2719])).
% 5.86/2.33  tff(c_179, plain, (![A_40, B_41, C_42]: (r1_tarski(A_40, k3_xboole_0(B_41, C_42)) | ~r1_tarski(A_40, C_42) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.86/2.33  tff(c_87, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 5.86/2.33  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.86/2.33  tff(c_152, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_18])).
% 5.86/2.33  tff(c_196, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_179, c_152])).
% 5.86/2.33  tff(c_270, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_196])).
% 5.86/2.33  tff(c_6510, plain, (~v1_funct_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6437, c_270])).
% 5.86/2.33  tff(c_6548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_119, c_20, c_6510])).
% 5.86/2.33  tff(c_6549, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_196])).
% 5.86/2.33  tff(c_6882, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_6549])).
% 5.86/2.33  tff(c_6886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_6882])).
% 5.86/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.33  
% 5.86/2.33  Inference rules
% 5.86/2.33  ----------------------
% 5.86/2.33  #Ref     : 0
% 5.86/2.33  #Sup     : 1608
% 5.86/2.33  #Fact    : 0
% 5.86/2.33  #Define  : 0
% 5.86/2.33  #Split   : 1
% 5.86/2.33  #Chain   : 0
% 5.86/2.33  #Close   : 0
% 5.86/2.33  
% 5.86/2.33  Ordering : KBO
% 5.86/2.33  
% 5.86/2.33  Simplification rules
% 5.86/2.33  ----------------------
% 5.86/2.33  #Subsume      : 169
% 5.86/2.33  #Demod        : 264
% 5.86/2.33  #Tautology    : 288
% 5.86/2.33  #SimpNegUnit  : 0
% 5.86/2.33  #BackRed      : 0
% 5.86/2.33  
% 5.86/2.33  #Partial instantiations: 0
% 5.86/2.33  #Strategies tried      : 1
% 5.86/2.33  
% 5.86/2.33  Timing (in seconds)
% 5.86/2.33  ----------------------
% 5.86/2.33  Preprocessing        : 0.28
% 5.86/2.33  Parsing              : 0.15
% 5.86/2.33  CNF conversion       : 0.02
% 5.86/2.33  Main loop            : 1.30
% 5.86/2.33  Inferencing          : 0.31
% 5.86/2.33  Reduction            : 0.51
% 5.86/2.33  Demodulation         : 0.44
% 5.86/2.33  BG Simplification    : 0.04
% 5.86/2.33  Subsumption          : 0.34
% 5.86/2.33  Abstraction          : 0.05
% 5.86/2.33  MUC search           : 0.00
% 5.86/2.33  Cooper               : 0.00
% 5.86/2.33  Total                : 1.60
% 5.86/2.33  Index Insertion      : 0.00
% 5.86/2.33  Index Deletion       : 0.00
% 5.86/2.33  Index Matching       : 0.00
% 5.86/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
