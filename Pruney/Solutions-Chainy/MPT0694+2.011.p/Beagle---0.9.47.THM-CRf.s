%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:54 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   49 (  78 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 108 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

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

tff(c_2988,plain,(
    ! [C_230,A_231,B_232] :
      ( r1_tarski(k9_relat_1(C_230,A_231),k9_relat_1(C_230,B_232))
      | ~ r1_tarski(A_231,B_232)
      | ~ v1_relat_1(C_230) ) ),
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

tff(c_14,plain,(
    ! [C_17,A_15,B_16] :
      ( r1_tarski(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16))
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_302,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k9_relat_1(B_55,k10_relat_1(B_55,A_56)),A_56)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_687,plain,(
    ! [A_91,A_92,B_93] :
      ( r1_tarski(A_91,A_92)
      | ~ r1_tarski(A_91,k9_relat_1(B_93,k10_relat_1(B_93,A_92)))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_302,c_6])).

tff(c_2643,plain,(
    ! [C_199,A_200,A_201] :
      ( r1_tarski(k9_relat_1(C_199,A_200),A_201)
      | ~ v1_funct_1(C_199)
      | ~ r1_tarski(A_200,k10_relat_1(C_199,A_201))
      | ~ v1_relat_1(C_199) ) ),
    inference(resolution,[status(thm)],[c_14,c_687])).

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

tff(c_2677,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2643,c_270])).

tff(c_2703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_119,c_20,c_2677])).

tff(c_2704,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_2991,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2988,c_2704])).

tff(c_2997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_2991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:32:17 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.82  
% 4.48/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.82  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.48/1.82  
% 4.48/1.82  %Foreground sorts:
% 4.48/1.82  
% 4.48/1.82  
% 4.48/1.82  %Background operators:
% 4.48/1.82  
% 4.48/1.82  
% 4.48/1.82  %Foreground operators:
% 4.48/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.48/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.48/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.48/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.48/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.48/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.48/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.48/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.48/1.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.48/1.82  
% 4.48/1.83  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 4.48/1.83  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.48/1.83  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 4.48/1.83  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.48/1.83  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.48/1.83  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 4.48/1.83  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.48/1.83  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.48/1.83  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.48/1.83  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.48/1.83  tff(c_2988, plain, (![C_230, A_231, B_232]: (r1_tarski(k9_relat_1(C_230, A_231), k9_relat_1(C_230, B_232)) | ~r1_tarski(A_231, B_232) | ~v1_relat_1(C_230))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.48/1.83  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.48/1.83  tff(c_57, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.48/1.83  tff(c_81, plain, (![B_28, A_29]: (k1_setfam_1(k2_tarski(B_28, A_29))=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_8, c_57])).
% 4.48/1.83  tff(c_12, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.48/1.83  tff(c_104, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 4.48/1.83  tff(c_119, plain, (![B_30, A_31]: (r1_tarski(k3_xboole_0(B_30, A_31), A_31))), inference(superposition, [status(thm), theory('equality')], [c_104, c_2])).
% 4.48/1.83  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.48/1.83  tff(c_14, plain, (![C_17, A_15, B_16]: (r1_tarski(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16)) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.48/1.83  tff(c_302, plain, (![B_55, A_56]: (r1_tarski(k9_relat_1(B_55, k10_relat_1(B_55, A_56)), A_56) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.48/1.83  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.48/1.83  tff(c_687, plain, (![A_91, A_92, B_93]: (r1_tarski(A_91, A_92) | ~r1_tarski(A_91, k9_relat_1(B_93, k10_relat_1(B_93, A_92))) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_302, c_6])).
% 4.48/1.83  tff(c_2643, plain, (![C_199, A_200, A_201]: (r1_tarski(k9_relat_1(C_199, A_200), A_201) | ~v1_funct_1(C_199) | ~r1_tarski(A_200, k10_relat_1(C_199, A_201)) | ~v1_relat_1(C_199))), inference(resolution, [status(thm)], [c_14, c_687])).
% 4.48/1.83  tff(c_179, plain, (![A_40, B_41, C_42]: (r1_tarski(A_40, k3_xboole_0(B_41, C_42)) | ~r1_tarski(A_40, C_42) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.48/1.83  tff(c_87, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 4.48/1.83  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.48/1.83  tff(c_152, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_18])).
% 4.48/1.83  tff(c_196, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_179, c_152])).
% 4.48/1.83  tff(c_270, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_196])).
% 4.48/1.83  tff(c_2677, plain, (~v1_funct_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2643, c_270])).
% 4.48/1.83  tff(c_2703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_119, c_20, c_2677])).
% 4.48/1.83  tff(c_2704, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_196])).
% 4.48/1.83  tff(c_2991, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2988, c_2704])).
% 4.48/1.83  tff(c_2997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_2991])).
% 4.48/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.83  
% 4.48/1.83  Inference rules
% 4.48/1.83  ----------------------
% 4.48/1.83  #Ref     : 0
% 4.48/1.83  #Sup     : 685
% 4.48/1.83  #Fact    : 0
% 4.48/1.83  #Define  : 0
% 4.48/1.83  #Split   : 1
% 4.48/1.83  #Chain   : 0
% 4.48/1.83  #Close   : 0
% 4.48/1.83  
% 4.48/1.83  Ordering : KBO
% 4.48/1.83  
% 4.48/1.83  Simplification rules
% 4.48/1.83  ----------------------
% 4.48/1.83  #Subsume      : 39
% 4.48/1.83  #Demod        : 140
% 4.48/1.83  #Tautology    : 159
% 4.48/1.83  #SimpNegUnit  : 0
% 4.48/1.83  #BackRed      : 0
% 4.48/1.83  
% 4.48/1.83  #Partial instantiations: 0
% 4.48/1.83  #Strategies tried      : 1
% 4.48/1.83  
% 4.48/1.83  Timing (in seconds)
% 4.48/1.83  ----------------------
% 4.48/1.84  Preprocessing        : 0.31
% 4.48/1.84  Parsing              : 0.17
% 4.48/1.84  CNF conversion       : 0.02
% 4.48/1.84  Main loop            : 0.75
% 4.48/1.84  Inferencing          : 0.21
% 4.48/1.84  Reduction            : 0.31
% 4.48/1.84  Demodulation         : 0.27
% 4.48/1.84  BG Simplification    : 0.03
% 4.48/1.84  Subsumption          : 0.15
% 4.48/1.84  Abstraction          : 0.03
% 4.48/1.84  MUC search           : 0.00
% 4.48/1.84  Cooper               : 0.00
% 4.48/1.84  Total                : 1.09
% 4.48/1.84  Index Insertion      : 0.00
% 4.48/1.84  Index Deletion       : 0.00
% 4.48/1.84  Index Matching       : 0.00
% 4.48/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
