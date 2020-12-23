%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:54 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   47 (  80 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 109 expanded)
%              Number of equality atoms :    9 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_191,plain,(
    ! [C_38,A_39,B_40] :
      ( r1_tarski(k9_relat_1(C_38,k3_xboole_0(A_39,B_40)),k3_xboole_0(k9_relat_1(C_38,A_39),k9_relat_1(C_38,B_40)))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_218,plain,(
    ! [C_38,A_39,B_40] :
      ( r1_tarski(k9_relat_1(C_38,k3_xboole_0(A_39,B_40)),k9_relat_1(C_38,A_39))
      | ~ v1_relat_1(C_38) ) ),
    inference(resolution,[status(thm)],[c_191,c_2])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_18,B_19] : k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [B_20,A_21] : k1_setfam_1(k2_tarski(B_20,A_21)) = k3_xboole_0(A_21,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_8,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [B_20,A_21] : k3_xboole_0(B_20,A_21) = k3_xboole_0(A_21,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_8])).

tff(c_219,plain,(
    ! [C_41,A_42,B_43] :
      ( r1_tarski(k9_relat_1(C_41,k3_xboole_0(A_42,B_43)),k9_relat_1(C_41,A_42))
      | ~ v1_relat_1(C_41) ) ),
    inference(resolution,[status(thm)],[c_191,c_2])).

tff(c_158,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,k9_relat_1(B_34,k1_relat_1(B_34))) = k9_relat_1(B_34,k10_relat_1(B_34,A_33))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,(
    ! [A_1,A_33,B_34] :
      ( r1_tarski(A_1,A_33)
      | ~ r1_tarski(A_1,k9_relat_1(B_34,k10_relat_1(B_34,A_33)))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_2])).

tff(c_250,plain,(
    ! [C_47,A_48,B_49] :
      ( r1_tarski(k9_relat_1(C_47,k3_xboole_0(k10_relat_1(C_47,A_48),B_49)),A_48)
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_219,c_176])).

tff(c_278,plain,(
    ! [C_50,B_51,A_52] :
      ( r1_tarski(k9_relat_1(C_50,k3_xboole_0(B_51,k10_relat_1(C_50,A_52))),A_52)
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_250])).

tff(c_139,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_tarski(A_30,k3_xboole_0(B_31,C_32))
      | ~ r1_tarski(A_30,C_32)
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_14])).

tff(c_156,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_139,c_131])).

tff(c_249,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_281,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_249])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_281])).

tff(c_306,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_315,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_218,c_306])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:50:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.29  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.29  
% 2.09/1.29  %Foreground sorts:
% 2.09/1.29  
% 2.09/1.29  
% 2.09/1.29  %Background operators:
% 2.09/1.29  
% 2.09/1.29  
% 2.09/1.29  %Foreground operators:
% 2.09/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.09/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.09/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.29  
% 2.09/1.30  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 2.09/1.30  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 2.09/1.30  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.09/1.30  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.09/1.30  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.09/1.30  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 2.09/1.30  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.09/1.30  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.30  tff(c_191, plain, (![C_38, A_39, B_40]: (r1_tarski(k9_relat_1(C_38, k3_xboole_0(A_39, B_40)), k3_xboole_0(k9_relat_1(C_38, A_39), k9_relat_1(C_38, B_40))) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.30  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.30  tff(c_218, plain, (![C_38, A_39, B_40]: (r1_tarski(k9_relat_1(C_38, k3_xboole_0(A_39, B_40)), k9_relat_1(C_38, A_39)) | ~v1_relat_1(C_38))), inference(resolution, [status(thm)], [c_191, c_2])).
% 2.09/1.30  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.30  tff(c_6, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.30  tff(c_52, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.30  tff(c_67, plain, (![B_20, A_21]: (k1_setfam_1(k2_tarski(B_20, A_21))=k3_xboole_0(A_21, B_20))), inference(superposition, [status(thm), theory('equality')], [c_6, c_52])).
% 2.09/1.30  tff(c_8, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.30  tff(c_73, plain, (![B_20, A_21]: (k3_xboole_0(B_20, A_21)=k3_xboole_0(A_21, B_20))), inference(superposition, [status(thm), theory('equality')], [c_67, c_8])).
% 2.09/1.30  tff(c_219, plain, (![C_41, A_42, B_43]: (r1_tarski(k9_relat_1(C_41, k3_xboole_0(A_42, B_43)), k9_relat_1(C_41, A_42)) | ~v1_relat_1(C_41))), inference(resolution, [status(thm)], [c_191, c_2])).
% 2.09/1.30  tff(c_158, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k9_relat_1(B_34, k1_relat_1(B_34)))=k9_relat_1(B_34, k10_relat_1(B_34, A_33)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.30  tff(c_176, plain, (![A_1, A_33, B_34]: (r1_tarski(A_1, A_33) | ~r1_tarski(A_1, k9_relat_1(B_34, k10_relat_1(B_34, A_33))) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_158, c_2])).
% 2.09/1.30  tff(c_250, plain, (![C_47, A_48, B_49]: (r1_tarski(k9_relat_1(C_47, k3_xboole_0(k10_relat_1(C_47, A_48), B_49)), A_48) | ~v1_funct_1(C_47) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_219, c_176])).
% 2.09/1.30  tff(c_278, plain, (![C_50, B_51, A_52]: (r1_tarski(k9_relat_1(C_50, k3_xboole_0(B_51, k10_relat_1(C_50, A_52))), A_52) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_73, c_250])).
% 2.09/1.30  tff(c_139, plain, (![A_30, B_31, C_32]: (r1_tarski(A_30, k3_xboole_0(B_31, C_32)) | ~r1_tarski(A_30, C_32) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.30  tff(c_14, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.30  tff(c_131, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_14])).
% 2.09/1.30  tff(c_156, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_139, c_131])).
% 2.09/1.30  tff(c_249, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_156])).
% 2.09/1.30  tff(c_281, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_278, c_249])).
% 2.09/1.30  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_281])).
% 2.09/1.30  tff(c_306, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_156])).
% 2.09/1.30  tff(c_315, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_218, c_306])).
% 2.09/1.30  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_315])).
% 2.09/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  Inference rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Ref     : 0
% 2.09/1.30  #Sup     : 74
% 2.09/1.30  #Fact    : 0
% 2.09/1.30  #Define  : 0
% 2.09/1.30  #Split   : 1
% 2.09/1.30  #Chain   : 0
% 2.09/1.30  #Close   : 0
% 2.09/1.30  
% 2.09/1.30  Ordering : KBO
% 2.09/1.30  
% 2.09/1.30  Simplification rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Subsume      : 10
% 2.09/1.30  #Demod        : 7
% 2.09/1.30  #Tautology    : 28
% 2.09/1.30  #SimpNegUnit  : 0
% 2.09/1.30  #BackRed      : 0
% 2.09/1.30  
% 2.09/1.30  #Partial instantiations: 0
% 2.09/1.30  #Strategies tried      : 1
% 2.09/1.30  
% 2.09/1.30  Timing (in seconds)
% 2.09/1.30  ----------------------
% 2.09/1.30  Preprocessing        : 0.26
% 2.09/1.30  Parsing              : 0.15
% 2.09/1.30  CNF conversion       : 0.02
% 2.09/1.30  Main loop            : 0.22
% 2.09/1.30  Inferencing          : 0.09
% 2.09/1.30  Reduction            : 0.07
% 2.09/1.30  Demodulation         : 0.05
% 2.09/1.30  BG Simplification    : 0.01
% 2.09/1.30  Subsumption          : 0.05
% 2.09/1.30  Abstraction          : 0.01
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.51
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
