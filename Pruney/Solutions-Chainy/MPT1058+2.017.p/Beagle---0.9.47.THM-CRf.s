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
% DateTime   : Thu Dec  3 10:17:24 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   50 (  53 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  47 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_69,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_58,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [B_28,A_27] : k2_tarski(B_28,A_27) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_153,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_183,plain,(
    ! [B_66,A_67] : k1_setfam_1(k2_tarski(B_66,A_67)) = k3_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_153])).

tff(c_52,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_189,plain,(
    ! [B_66,A_67] : k3_xboole_0(B_66,A_67) = k3_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_52])).

tff(c_60,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_357,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_xboole_0(A_82,k4_xboole_0(C_83,B_84))
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1879,plain,(
    ! [A_177,C_178,B_179] :
      ( k4_xboole_0(A_177,k4_xboole_0(C_178,B_179)) = A_177
      | ~ r1_tarski(A_177,B_179) ) ),
    inference(resolution,[status(thm)],[c_357,c_38])).

tff(c_36,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2039,plain,(
    ! [C_182,B_183] :
      ( k3_xboole_0(C_182,B_183) = C_182
      | ~ r1_tarski(C_182,B_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1879,c_36])).

tff(c_2128,plain,(
    k3_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_2039])).

tff(c_2349,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_2128])).

tff(c_54,plain,(
    ! [A_40,C_42,B_41] :
      ( k3_xboole_0(A_40,k10_relat_1(C_42,B_41)) = k10_relat_1(k7_relat_1(C_42,A_40),B_41)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2562,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2349,c_54])).

tff(c_2605,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2562])).

tff(c_2607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.64  
% 3.63/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.63/1.64  
% 3.63/1.64  %Foreground sorts:
% 3.63/1.64  
% 3.63/1.64  
% 3.63/1.64  %Background operators:
% 3.63/1.64  
% 3.63/1.64  
% 3.63/1.64  %Foreground operators:
% 3.63/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.63/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.63/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.63/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.63/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.63/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.63/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.63/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.63/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.63/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.63/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.63/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.63/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.63/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.63/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.63/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.63/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.63/1.64  
% 3.97/1.65  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.97/1.65  tff(f_69, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.97/1.65  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.97/1.65  tff(f_67, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.97/1.65  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.97/1.65  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.97/1.65  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.97/1.65  tff(c_58, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.97/1.65  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.97/1.65  tff(c_44, plain, (![B_28, A_27]: (k2_tarski(B_28, A_27)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.97/1.65  tff(c_153, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.97/1.65  tff(c_183, plain, (![B_66, A_67]: (k1_setfam_1(k2_tarski(B_66, A_67))=k3_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_44, c_153])).
% 3.97/1.65  tff(c_52, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.97/1.65  tff(c_189, plain, (![B_66, A_67]: (k3_xboole_0(B_66, A_67)=k3_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_183, c_52])).
% 3.97/1.65  tff(c_60, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.97/1.65  tff(c_357, plain, (![A_82, C_83, B_84]: (r1_xboole_0(A_82, k4_xboole_0(C_83, B_84)) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.97/1.65  tff(c_38, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.65  tff(c_1879, plain, (![A_177, C_178, B_179]: (k4_xboole_0(A_177, k4_xboole_0(C_178, B_179))=A_177 | ~r1_tarski(A_177, B_179))), inference(resolution, [status(thm)], [c_357, c_38])).
% 3.97/1.65  tff(c_36, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.65  tff(c_2039, plain, (![C_182, B_183]: (k3_xboole_0(C_182, B_183)=C_182 | ~r1_tarski(C_182, B_183))), inference(superposition, [status(thm), theory('equality')], [c_1879, c_36])).
% 3.97/1.65  tff(c_2128, plain, (k3_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_2039])).
% 3.97/1.65  tff(c_2349, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_189, c_2128])).
% 3.97/1.65  tff(c_54, plain, (![A_40, C_42, B_41]: (k3_xboole_0(A_40, k10_relat_1(C_42, B_41))=k10_relat_1(k7_relat_1(C_42, A_40), B_41) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.97/1.65  tff(c_2562, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2349, c_54])).
% 3.97/1.65  tff(c_2605, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2562])).
% 3.97/1.65  tff(c_2607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2605])).
% 3.97/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.65  
% 3.97/1.65  Inference rules
% 3.97/1.65  ----------------------
% 3.97/1.65  #Ref     : 0
% 3.97/1.66  #Sup     : 598
% 3.97/1.66  #Fact    : 0
% 3.97/1.66  #Define  : 0
% 3.97/1.66  #Split   : 0
% 3.97/1.66  #Chain   : 0
% 3.97/1.66  #Close   : 0
% 3.97/1.66  
% 3.97/1.66  Ordering : KBO
% 3.97/1.66  
% 3.97/1.66  Simplification rules
% 3.97/1.66  ----------------------
% 3.97/1.66  #Subsume      : 30
% 3.97/1.66  #Demod        : 376
% 3.97/1.66  #Tautology    : 347
% 3.97/1.66  #SimpNegUnit  : 1
% 3.97/1.66  #BackRed      : 0
% 3.97/1.66  
% 3.97/1.66  #Partial instantiations: 0
% 3.97/1.66  #Strategies tried      : 1
% 3.97/1.66  
% 3.97/1.66  Timing (in seconds)
% 3.97/1.66  ----------------------
% 3.97/1.66  Preprocessing        : 0.32
% 3.97/1.66  Parsing              : 0.17
% 3.97/1.66  CNF conversion       : 0.02
% 3.97/1.66  Main loop            : 0.57
% 3.97/1.66  Inferencing          : 0.18
% 3.97/1.66  Reduction            : 0.23
% 3.97/1.66  Demodulation         : 0.19
% 3.97/1.66  BG Simplification    : 0.03
% 3.97/1.66  Subsumption          : 0.09
% 3.97/1.66  Abstraction          : 0.03
% 3.97/1.66  MUC search           : 0.00
% 3.97/1.66  Cooper               : 0.00
% 3.97/1.66  Total                : 0.91
% 3.97/1.66  Index Insertion      : 0.00
% 3.97/1.66  Index Deletion       : 0.00
% 3.97/1.66  Index Matching       : 0.00
% 3.97/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
