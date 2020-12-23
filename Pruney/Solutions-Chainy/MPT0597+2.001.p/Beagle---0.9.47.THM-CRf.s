%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:12 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  61 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( k7_relat_1(B,A) = k7_relat_1(C,A)
             => k9_relat_1(B,A) = k9_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_52,B_53] : k4_xboole_0(k2_xboole_0(A_52,B_53),k3_xboole_0(A_52,B_53)) = k5_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [A_1] : k4_xboole_0(A_1,k3_xboole_0(A_1,A_1)) = k5_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_164,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14,c_161])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    k7_relat_1('#skF_2','#skF_1') = k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_317,plain,(
    ! [A_63,C_64,B_65] :
      ( k9_relat_1(k7_relat_1(A_63,C_64),B_65) = k9_relat_1(A_63,B_65)
      | ~ r1_tarski(B_65,C_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_326,plain,(
    ! [B_65] :
      ( k9_relat_1(k7_relat_1('#skF_3','#skF_1'),B_65) = k9_relat_1('#skF_2',B_65)
      | ~ r1_tarski(B_65,'#skF_1')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_317])).

tff(c_419,plain,(
    ! [B_69] :
      ( k9_relat_1(k7_relat_1('#skF_3','#skF_1'),B_69) = k9_relat_1('#skF_2',B_69)
      | ~ r1_tarski(B_69,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_326])).

tff(c_26,plain,(
    ! [A_25,C_29,B_28] :
      ( k9_relat_1(k7_relat_1(A_25,C_29),B_28) = k9_relat_1(A_25,B_28)
      | ~ r1_tarski(B_28,C_29)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_425,plain,(
    ! [B_69] :
      ( k9_relat_1('#skF_2',B_69) = k9_relat_1('#skF_3',B_69)
      | ~ r1_tarski(B_69,'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(B_69,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_26])).

tff(c_501,plain,(
    ! [B_72] :
      ( k9_relat_1('#skF_2',B_72) = k9_relat_1('#skF_3',B_72)
      | ~ r1_tarski(B_72,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_425])).

tff(c_601,plain,(
    ! [A_77] :
      ( k9_relat_1('#skF_2',A_77) = k9_relat_1('#skF_3',A_77)
      | k4_xboole_0(A_77,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_501])).

tff(c_28,plain,(
    k9_relat_1('#skF_2','#skF_1') != k9_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_607,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_28])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  %$ r1_tarski > v1_relat_1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.34/1.32  
% 2.34/1.32  %Foreground sorts:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Background operators:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Foreground operators:
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.34/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.34/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.34/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.32  
% 2.34/1.33  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.34/1.33  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.34/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.34/1.33  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 2.34/1.33  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.34/1.33  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k7_relat_1(B, A) = k7_relat_1(C, A)) => (k9_relat_1(B, A) = k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_relat_1)).
% 2.34/1.33  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.34/1.33  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.33  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.33  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.33  tff(c_146, plain, (![A_52, B_53]: (k4_xboole_0(k2_xboole_0(A_52, B_53), k3_xboole_0(A_52, B_53))=k5_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.33  tff(c_161, plain, (![A_1]: (k4_xboole_0(A_1, k3_xboole_0(A_1, A_1))=k5_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_146])).
% 2.34/1.33  tff(c_164, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14, c_161])).
% 2.34/1.33  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.33  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.33  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.33  tff(c_30, plain, (k7_relat_1('#skF_2', '#skF_1')=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.33  tff(c_317, plain, (![A_63, C_64, B_65]: (k9_relat_1(k7_relat_1(A_63, C_64), B_65)=k9_relat_1(A_63, B_65) | ~r1_tarski(B_65, C_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.34/1.33  tff(c_326, plain, (![B_65]: (k9_relat_1(k7_relat_1('#skF_3', '#skF_1'), B_65)=k9_relat_1('#skF_2', B_65) | ~r1_tarski(B_65, '#skF_1') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_317])).
% 2.34/1.33  tff(c_419, plain, (![B_69]: (k9_relat_1(k7_relat_1('#skF_3', '#skF_1'), B_69)=k9_relat_1('#skF_2', B_69) | ~r1_tarski(B_69, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_326])).
% 2.34/1.33  tff(c_26, plain, (![A_25, C_29, B_28]: (k9_relat_1(k7_relat_1(A_25, C_29), B_28)=k9_relat_1(A_25, B_28) | ~r1_tarski(B_28, C_29) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.34/1.33  tff(c_425, plain, (![B_69]: (k9_relat_1('#skF_2', B_69)=k9_relat_1('#skF_3', B_69) | ~r1_tarski(B_69, '#skF_1') | ~v1_relat_1('#skF_3') | ~r1_tarski(B_69, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_419, c_26])).
% 2.34/1.33  tff(c_501, plain, (![B_72]: (k9_relat_1('#skF_2', B_72)=k9_relat_1('#skF_3', B_72) | ~r1_tarski(B_72, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_425])).
% 2.34/1.33  tff(c_601, plain, (![A_77]: (k9_relat_1('#skF_2', A_77)=k9_relat_1('#skF_3', A_77) | k4_xboole_0(A_77, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_501])).
% 2.34/1.33  tff(c_28, plain, (k9_relat_1('#skF_2', '#skF_1')!=k9_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.33  tff(c_607, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_601, c_28])).
% 2.34/1.33  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_607])).
% 2.34/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.33  
% 2.34/1.33  Inference rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Ref     : 0
% 2.34/1.33  #Sup     : 142
% 2.34/1.33  #Fact    : 0
% 2.34/1.33  #Define  : 0
% 2.34/1.33  #Split   : 0
% 2.34/1.33  #Chain   : 0
% 2.34/1.33  #Close   : 0
% 2.34/1.33  
% 2.34/1.33  Ordering : KBO
% 2.34/1.33  
% 2.34/1.33  Simplification rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Subsume      : 7
% 2.34/1.33  #Demod        : 105
% 2.34/1.33  #Tautology    : 107
% 2.34/1.33  #SimpNegUnit  : 0
% 2.34/1.33  #BackRed      : 0
% 2.34/1.33  
% 2.34/1.33  #Partial instantiations: 0
% 2.34/1.33  #Strategies tried      : 1
% 2.34/1.33  
% 2.34/1.33  Timing (in seconds)
% 2.34/1.33  ----------------------
% 2.34/1.34  Preprocessing        : 0.29
% 2.34/1.34  Parsing              : 0.15
% 2.34/1.34  CNF conversion       : 0.02
% 2.34/1.34  Main loop            : 0.26
% 2.34/1.34  Inferencing          : 0.10
% 2.34/1.34  Reduction            : 0.09
% 2.34/1.34  Demodulation         : 0.07
% 2.34/1.34  BG Simplification    : 0.01
% 2.34/1.34  Subsumption          : 0.03
% 2.34/1.34  Abstraction          : 0.01
% 2.34/1.34  MUC search           : 0.00
% 2.34/1.34  Cooper               : 0.00
% 2.34/1.34  Total                : 0.57
% 2.34/1.34  Index Insertion      : 0.00
% 2.34/1.34  Index Deletion       : 0.00
% 2.34/1.34  Index Matching       : 0.00
% 2.34/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
