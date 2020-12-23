%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:54 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   52 (  92 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 126 expanded)
%              Number of equality atoms :   11 (  36 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1312,plain,(
    ! [C_121,A_122,B_123] :
      ( r1_tarski(k9_relat_1(C_121,k3_xboole_0(A_122,B_123)),k3_xboole_0(k9_relat_1(C_121,A_122),k9_relat_1(C_121,B_123)))
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1343,plain,(
    ! [C_124,A_125,B_126] :
      ( r1_tarski(k9_relat_1(C_124,k3_xboole_0(A_125,B_126)),k9_relat_1(C_124,A_125))
      | ~ v1_relat_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_1312,c_2])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

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

tff(c_87,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_351,plain,(
    ! [C_55,A_56,B_57] :
      ( r1_tarski(k9_relat_1(C_55,k3_xboole_0(A_56,B_57)),k3_xboole_0(k9_relat_1(C_55,A_56),k9_relat_1(C_55,B_57)))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_382,plain,(
    ! [C_58,A_59,B_60] :
      ( r1_tarski(k9_relat_1(C_58,k3_xboole_0(A_59,B_60)),k9_relat_1(C_58,A_59))
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_351,c_2])).

tff(c_394,plain,(
    ! [C_58,B_28,A_29] :
      ( r1_tarski(k9_relat_1(C_58,k3_xboole_0(B_28,A_29)),k9_relat_1(C_58,A_29))
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_382])).

tff(c_176,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k9_relat_1(B_41,k10_relat_1(B_41,A_42)),A_42)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_187,plain,(
    ! [B_41,A_42] :
      ( k3_xboole_0(k9_relat_1(B_41,k10_relat_1(B_41,A_42)),A_42) = k9_relat_1(B_41,k10_relat_1(B_41,A_42))
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_176,c_6])).

tff(c_1085,plain,(
    ! [A_113,B_114] :
      ( k3_xboole_0(A_113,k9_relat_1(B_114,k10_relat_1(B_114,A_113))) = k9_relat_1(B_114,k10_relat_1(B_114,A_113))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_187])).

tff(c_1198,plain,(
    ! [A_115,A_116,B_117] :
      ( r1_tarski(A_115,A_116)
      | ~ r1_tarski(A_115,k9_relat_1(B_117,k10_relat_1(B_117,A_116)))
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_2])).

tff(c_1259,plain,(
    ! [C_118,B_119,A_120] :
      ( r1_tarski(k9_relat_1(C_118,k3_xboole_0(B_119,k10_relat_1(C_118,A_120))),A_120)
      | ~ v1_funct_1(C_118)
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_394,c_1198])).

tff(c_153,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,k3_xboole_0(B_39,C_40))
      | ~ r1_tarski(A_38,C_40)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_137,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_18])).

tff(c_174,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_153,c_137])).

tff(c_294,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_1274,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1259,c_294])).

tff(c_1305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_1274])).

tff(c_1306,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_1346,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1343,c_1306])).

tff(c_1365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:09:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.54  
% 3.25/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.54  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.25/1.54  
% 3.25/1.54  %Foreground sorts:
% 3.25/1.54  
% 3.25/1.54  
% 3.25/1.54  %Background operators:
% 3.25/1.54  
% 3.25/1.54  
% 3.25/1.54  %Foreground operators:
% 3.25/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.25/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.25/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.25/1.54  
% 3.42/1.55  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 3.42/1.55  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 3.42/1.55  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.42/1.55  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.42/1.55  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.42/1.55  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.42/1.55  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.42/1.55  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.42/1.55  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.42/1.55  tff(c_1312, plain, (![C_121, A_122, B_123]: (r1_tarski(k9_relat_1(C_121, k3_xboole_0(A_122, B_123)), k3_xboole_0(k9_relat_1(C_121, A_122), k9_relat_1(C_121, B_123))) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.42/1.55  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.55  tff(c_1343, plain, (![C_124, A_125, B_126]: (r1_tarski(k9_relat_1(C_124, k3_xboole_0(A_125, B_126)), k9_relat_1(C_124, A_125)) | ~v1_relat_1(C_124))), inference(resolution, [status(thm)], [c_1312, c_2])).
% 3.42/1.55  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.42/1.55  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.42/1.55  tff(c_57, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.55  tff(c_81, plain, (![B_28, A_29]: (k1_setfam_1(k2_tarski(B_28, A_29))=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_8, c_57])).
% 3.42/1.55  tff(c_12, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.55  tff(c_87, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 3.42/1.55  tff(c_351, plain, (![C_55, A_56, B_57]: (r1_tarski(k9_relat_1(C_55, k3_xboole_0(A_56, B_57)), k3_xboole_0(k9_relat_1(C_55, A_56), k9_relat_1(C_55, B_57))) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.42/1.55  tff(c_382, plain, (![C_58, A_59, B_60]: (r1_tarski(k9_relat_1(C_58, k3_xboole_0(A_59, B_60)), k9_relat_1(C_58, A_59)) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_351, c_2])).
% 3.42/1.55  tff(c_394, plain, (![C_58, B_28, A_29]: (r1_tarski(k9_relat_1(C_58, k3_xboole_0(B_28, A_29)), k9_relat_1(C_58, A_29)) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_87, c_382])).
% 3.42/1.55  tff(c_176, plain, (![B_41, A_42]: (r1_tarski(k9_relat_1(B_41, k10_relat_1(B_41, A_42)), A_42) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.42/1.55  tff(c_6, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.55  tff(c_187, plain, (![B_41, A_42]: (k3_xboole_0(k9_relat_1(B_41, k10_relat_1(B_41, A_42)), A_42)=k9_relat_1(B_41, k10_relat_1(B_41, A_42)) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_176, c_6])).
% 3.42/1.55  tff(c_1085, plain, (![A_113, B_114]: (k3_xboole_0(A_113, k9_relat_1(B_114, k10_relat_1(B_114, A_113)))=k9_relat_1(B_114, k10_relat_1(B_114, A_113)) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_187])).
% 3.42/1.55  tff(c_1198, plain, (![A_115, A_116, B_117]: (r1_tarski(A_115, A_116) | ~r1_tarski(A_115, k9_relat_1(B_117, k10_relat_1(B_117, A_116))) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_1085, c_2])).
% 3.42/1.55  tff(c_1259, plain, (![C_118, B_119, A_120]: (r1_tarski(k9_relat_1(C_118, k3_xboole_0(B_119, k10_relat_1(C_118, A_120))), A_120) | ~v1_funct_1(C_118) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_394, c_1198])).
% 3.42/1.55  tff(c_153, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, k3_xboole_0(B_39, C_40)) | ~r1_tarski(A_38, C_40) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.55  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.42/1.55  tff(c_137, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_18])).
% 3.42/1.55  tff(c_174, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_153, c_137])).
% 3.42/1.55  tff(c_294, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_174])).
% 3.42/1.55  tff(c_1274, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1259, c_294])).
% 3.42/1.55  tff(c_1305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_1274])).
% 3.42/1.55  tff(c_1306, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_174])).
% 3.42/1.55  tff(c_1346, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1343, c_1306])).
% 3.42/1.55  tff(c_1365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1346])).
% 3.42/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  Inference rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Ref     : 0
% 3.42/1.55  #Sup     : 365
% 3.42/1.55  #Fact    : 0
% 3.42/1.55  #Define  : 0
% 3.42/1.55  #Split   : 1
% 3.42/1.55  #Chain   : 0
% 3.42/1.55  #Close   : 0
% 3.42/1.55  
% 3.42/1.55  Ordering : KBO
% 3.42/1.55  
% 3.42/1.55  Simplification rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Subsume      : 98
% 3.42/1.55  #Demod        : 26
% 3.42/1.55  #Tautology    : 53
% 3.42/1.55  #SimpNegUnit  : 0
% 3.42/1.55  #BackRed      : 0
% 3.42/1.55  
% 3.42/1.55  #Partial instantiations: 0
% 3.42/1.55  #Strategies tried      : 1
% 3.42/1.55  
% 3.42/1.55  Timing (in seconds)
% 3.42/1.55  ----------------------
% 3.42/1.55  Preprocessing        : 0.28
% 3.42/1.55  Parsing              : 0.15
% 3.42/1.55  CNF conversion       : 0.02
% 3.42/1.55  Main loop            : 0.47
% 3.42/1.55  Inferencing          : 0.17
% 3.42/1.55  Reduction            : 0.15
% 3.42/1.55  Demodulation         : 0.12
% 3.42/1.55  BG Simplification    : 0.02
% 3.42/1.55  Subsumption          : 0.11
% 3.42/1.55  Abstraction          : 0.03
% 3.42/1.55  MUC search           : 0.00
% 3.42/1.55  Cooper               : 0.00
% 3.42/1.55  Total                : 0.78
% 3.42/1.55  Index Insertion      : 0.00
% 3.42/1.55  Index Deletion       : 0.00
% 3.42/1.55  Index Matching       : 0.00
% 3.42/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
