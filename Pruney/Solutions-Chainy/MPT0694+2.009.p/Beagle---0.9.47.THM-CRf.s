%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:54 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 111 expanded)
%              Number of equality atoms :    7 (  24 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_464,plain,(
    ! [C_81,A_82,B_83] :
      ( r1_tarski(k9_relat_1(C_81,k3_xboole_0(A_82,B_83)),k3_xboole_0(k9_relat_1(C_81,A_82),k9_relat_1(C_81,B_83)))
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_488,plain,(
    ! [C_84,A_85,B_86] :
      ( r1_tarski(k9_relat_1(C_84,k3_xboole_0(A_85,B_86)),k9_relat_1(C_84,A_85))
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_464,c_2])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [B_30,A_31] : k1_setfam_1(k2_tarski(B_30,A_31)) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_56])).

tff(c_12,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [B_30,A_31] : k3_xboole_0(B_30,A_31) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_259,plain,(
    ! [C_58,A_59,B_60] :
      ( r1_tarski(k9_relat_1(C_58,k3_xboole_0(A_59,B_60)),k3_xboole_0(k9_relat_1(C_58,A_59),k9_relat_1(C_58,B_60)))
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_286,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(k9_relat_1(C_61,k3_xboole_0(A_62,B_63)),k9_relat_1(C_61,A_62))
      | ~ v1_relat_1(C_61) ) ),
    inference(resolution,[status(thm)],[c_259,c_2])).

tff(c_175,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(k9_relat_1(B_43,k10_relat_1(B_43,A_44)),A_44)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_186,plain,(
    ! [A_7,A_44,B_43] :
      ( r1_tarski(A_7,A_44)
      | ~ r1_tarski(A_7,k9_relat_1(B_43,k10_relat_1(B_43,A_44)))
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_175,c_6])).

tff(c_354,plain,(
    ! [C_71,A_72,B_73] :
      ( r1_tarski(k9_relat_1(C_71,k3_xboole_0(k10_relat_1(C_71,A_72),B_73)),A_72)
      | ~ v1_funct_1(C_71)
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_286,c_186])).

tff(c_420,plain,(
    ! [C_78,B_79,A_80] :
      ( r1_tarski(k9_relat_1(C_78,k3_xboole_0(B_79,k10_relat_1(C_78,A_80))),A_80)
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_354])).

tff(c_153,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(A_40,k3_xboole_0(B_41,C_42))
      | ~ r1_tarski(A_40,C_42)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_143,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_18])).

tff(c_173,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_153,c_143])).

tff(c_229,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_433,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_420,c_229])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_433])).

tff(c_459,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_491,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_488,c_459])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.42  
% 2.49/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.42  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.42  
% 2.49/1.42  %Foreground sorts:
% 2.49/1.42  
% 2.49/1.42  
% 2.49/1.42  %Background operators:
% 2.49/1.42  
% 2.49/1.42  
% 2.49/1.42  %Foreground operators:
% 2.49/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.49/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.49/1.42  
% 2.49/1.44  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 2.49/1.44  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 2.49/1.44  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.49/1.44  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.49/1.44  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.49/1.44  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.49/1.44  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.49/1.44  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.49/1.44  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.49/1.44  tff(c_464, plain, (![C_81, A_82, B_83]: (r1_tarski(k9_relat_1(C_81, k3_xboole_0(A_82, B_83)), k3_xboole_0(k9_relat_1(C_81, A_82), k9_relat_1(C_81, B_83))) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.49/1.44  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.44  tff(c_488, plain, (![C_84, A_85, B_86]: (r1_tarski(k9_relat_1(C_84, k3_xboole_0(A_85, B_86)), k9_relat_1(C_84, A_85)) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_464, c_2])).
% 2.49/1.44  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.49/1.44  tff(c_8, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.44  tff(c_56, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.44  tff(c_81, plain, (![B_30, A_31]: (k1_setfam_1(k2_tarski(B_30, A_31))=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_56])).
% 2.49/1.44  tff(c_12, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.44  tff(c_87, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 2.49/1.44  tff(c_259, plain, (![C_58, A_59, B_60]: (r1_tarski(k9_relat_1(C_58, k3_xboole_0(A_59, B_60)), k3_xboole_0(k9_relat_1(C_58, A_59), k9_relat_1(C_58, B_60))) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.49/1.44  tff(c_286, plain, (![C_61, A_62, B_63]: (r1_tarski(k9_relat_1(C_61, k3_xboole_0(A_62, B_63)), k9_relat_1(C_61, A_62)) | ~v1_relat_1(C_61))), inference(resolution, [status(thm)], [c_259, c_2])).
% 2.49/1.44  tff(c_175, plain, (![B_43, A_44]: (r1_tarski(k9_relat_1(B_43, k10_relat_1(B_43, A_44)), A_44) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.49/1.44  tff(c_6, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.44  tff(c_186, plain, (![A_7, A_44, B_43]: (r1_tarski(A_7, A_44) | ~r1_tarski(A_7, k9_relat_1(B_43, k10_relat_1(B_43, A_44))) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_175, c_6])).
% 2.49/1.44  tff(c_354, plain, (![C_71, A_72, B_73]: (r1_tarski(k9_relat_1(C_71, k3_xboole_0(k10_relat_1(C_71, A_72), B_73)), A_72) | ~v1_funct_1(C_71) | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_286, c_186])).
% 2.49/1.44  tff(c_420, plain, (![C_78, B_79, A_80]: (r1_tarski(k9_relat_1(C_78, k3_xboole_0(B_79, k10_relat_1(C_78, A_80))), A_80) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(superposition, [status(thm), theory('equality')], [c_87, c_354])).
% 2.49/1.44  tff(c_153, plain, (![A_40, B_41, C_42]: (r1_tarski(A_40, k3_xboole_0(B_41, C_42)) | ~r1_tarski(A_40, C_42) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.44  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.49/1.44  tff(c_143, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_18])).
% 2.49/1.44  tff(c_173, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_153, c_143])).
% 2.49/1.44  tff(c_229, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_173])).
% 2.49/1.44  tff(c_433, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_420, c_229])).
% 2.49/1.44  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_433])).
% 2.49/1.44  tff(c_459, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_173])).
% 2.49/1.44  tff(c_491, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_488, c_459])).
% 2.49/1.44  tff(c_503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_491])).
% 2.49/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.44  
% 2.49/1.44  Inference rules
% 2.49/1.44  ----------------------
% 2.49/1.44  #Ref     : 0
% 2.49/1.44  #Sup     : 120
% 2.49/1.44  #Fact    : 0
% 2.49/1.44  #Define  : 0
% 2.49/1.44  #Split   : 1
% 2.49/1.44  #Chain   : 0
% 2.49/1.44  #Close   : 0
% 2.49/1.44  
% 2.49/1.44  Ordering : KBO
% 2.49/1.44  
% 2.49/1.44  Simplification rules
% 2.49/1.44  ----------------------
% 2.49/1.44  #Subsume      : 14
% 2.49/1.44  #Demod        : 7
% 2.49/1.44  #Tautology    : 27
% 2.49/1.44  #SimpNegUnit  : 0
% 2.49/1.44  #BackRed      : 0
% 2.49/1.44  
% 2.49/1.44  #Partial instantiations: 0
% 2.49/1.44  #Strategies tried      : 1
% 2.49/1.44  
% 2.49/1.44  Timing (in seconds)
% 2.49/1.44  ----------------------
% 2.49/1.44  Preprocessing        : 0.36
% 2.49/1.44  Parsing              : 0.19
% 2.49/1.44  CNF conversion       : 0.02
% 2.49/1.44  Main loop            : 0.27
% 2.49/1.44  Inferencing          : 0.10
% 2.49/1.44  Reduction            : 0.08
% 2.49/1.44  Demodulation         : 0.07
% 2.49/1.44  BG Simplification    : 0.02
% 2.49/1.44  Subsumption          : 0.06
% 2.49/1.44  Abstraction          : 0.02
% 2.49/1.44  MUC search           : 0.00
% 2.49/1.44  Cooper               : 0.00
% 2.49/1.44  Total                : 0.67
% 2.49/1.44  Index Insertion      : 0.00
% 2.49/1.44  Index Deletion       : 0.00
% 2.49/1.44  Index Matching       : 0.00
% 2.49/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
