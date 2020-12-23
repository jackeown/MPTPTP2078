%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:03 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   58 (  61 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 (  72 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_177,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k4_xboole_0(B_43,A_42)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_186,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_177])).

tff(c_189,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_186])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_270,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_288,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,'#skF_2')
      | ~ r1_tarski(A_52,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_270])).

tff(c_22,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_240,plain,(
    ! [B_49,A_50] :
      ( ~ r1_xboole_0(B_49,A_50)
      | ~ r1_tarski(B_49,A_50)
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_550,plain,(
    ! [A_84,B_85] :
      ( ~ r1_tarski(k4_xboole_0(A_84,B_85),B_85)
      | v1_xboole_0(k4_xboole_0(A_84,B_85)) ) ),
    inference(resolution,[status(thm)],[c_22,c_240])).

tff(c_651,plain,(
    ! [A_88] :
      ( v1_xboole_0(k4_xboole_0(A_88,'#skF_2'))
      | ~ r1_tarski(k4_xboole_0(A_88,'#skF_2'),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_288,c_550])).

tff(c_671,plain,(
    v1_xboole_0(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_651])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_165,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | B_39 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_168,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_679,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_671,c_168])).

tff(c_28,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_763,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_28])).

tff(c_780,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_2,c_763])).

tff(c_400,plain,(
    ! [C_68,A_69,B_70] :
      ( k2_xboole_0(k9_relat_1(C_68,A_69),k9_relat_1(C_68,B_70)) = k9_relat_1(C_68,k2_xboole_0(A_69,B_70))
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1182,plain,(
    ! [C_103,A_104,B_105] :
      ( r1_tarski(k9_relat_1(C_103,A_104),k9_relat_1(C_103,k2_xboole_0(A_104,B_105)))
      | ~ v1_relat_1(C_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_24])).

tff(c_2569,plain,(
    ! [C_153] :
      ( r1_tarski(k9_relat_1(C_153,'#skF_1'),k9_relat_1(C_153,'#skF_2'))
      | ~ v1_relat_1(C_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_1182])).

tff(c_32,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2578,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2569,c_32])).

tff(c_2585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.59  
% 3.57/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.59  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.57/1.59  
% 3.57/1.59  %Foreground sorts:
% 3.57/1.59  
% 3.57/1.59  
% 3.57/1.59  %Background operators:
% 3.57/1.59  
% 3.57/1.59  
% 3.57/1.59  %Foreground operators:
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.57/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.57/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.57/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.57/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.57/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.59  
% 3.70/1.60  tff(f_79, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 3.70/1.60  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.70/1.60  tff(f_46, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.70/1.60  tff(f_68, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.70/1.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.70/1.60  tff(f_44, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.70/1.60  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.70/1.60  tff(f_56, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.70/1.60  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.70/1.60  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.70/1.60  tff(f_66, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.70/1.60  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 3.70/1.60  tff(f_58, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.70/1.60  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.70/1.60  tff(c_12, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.70/1.60  tff(c_18, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.70/1.60  tff(c_177, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k4_xboole_0(B_43, A_42))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.60  tff(c_186, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_177])).
% 3.70/1.60  tff(c_189, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_186])).
% 3.70/1.60  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/1.60  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.70/1.60  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.70/1.60  tff(c_270, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.70/1.60  tff(c_288, plain, (![A_52]: (r1_tarski(A_52, '#skF_2') | ~r1_tarski(A_52, '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_270])).
% 3.70/1.60  tff(c_22, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.70/1.60  tff(c_240, plain, (![B_49, A_50]: (~r1_xboole_0(B_49, A_50) | ~r1_tarski(B_49, A_50) | v1_xboole_0(B_49))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.70/1.60  tff(c_550, plain, (![A_84, B_85]: (~r1_tarski(k4_xboole_0(A_84, B_85), B_85) | v1_xboole_0(k4_xboole_0(A_84, B_85)))), inference(resolution, [status(thm)], [c_22, c_240])).
% 3.70/1.60  tff(c_651, plain, (![A_88]: (v1_xboole_0(k4_xboole_0(A_88, '#skF_2')) | ~r1_tarski(k4_xboole_0(A_88, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_288, c_550])).
% 3.70/1.60  tff(c_671, plain, (v1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_651])).
% 3.70/1.60  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.70/1.60  tff(c_165, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | B_39=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.70/1.60  tff(c_168, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_4, c_165])).
% 3.70/1.60  tff(c_679, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_671, c_168])).
% 3.70/1.60  tff(c_28, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.60  tff(c_763, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_679, c_28])).
% 3.70/1.60  tff(c_780, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_2, c_763])).
% 3.70/1.60  tff(c_400, plain, (![C_68, A_69, B_70]: (k2_xboole_0(k9_relat_1(C_68, A_69), k9_relat_1(C_68, B_70))=k9_relat_1(C_68, k2_xboole_0(A_69, B_70)) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.70/1.60  tff(c_24, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.60  tff(c_1182, plain, (![C_103, A_104, B_105]: (r1_tarski(k9_relat_1(C_103, A_104), k9_relat_1(C_103, k2_xboole_0(A_104, B_105))) | ~v1_relat_1(C_103))), inference(superposition, [status(thm), theory('equality')], [c_400, c_24])).
% 3.70/1.60  tff(c_2569, plain, (![C_153]: (r1_tarski(k9_relat_1(C_153, '#skF_1'), k9_relat_1(C_153, '#skF_2')) | ~v1_relat_1(C_153))), inference(superposition, [status(thm), theory('equality')], [c_780, c_1182])).
% 3.70/1.60  tff(c_32, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.70/1.60  tff(c_2578, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2569, c_32])).
% 3.70/1.60  tff(c_2585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2578])).
% 3.70/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.60  
% 3.70/1.60  Inference rules
% 3.70/1.60  ----------------------
% 3.70/1.60  #Ref     : 0
% 3.70/1.60  #Sup     : 614
% 3.70/1.60  #Fact    : 0
% 3.70/1.60  #Define  : 0
% 3.70/1.60  #Split   : 1
% 3.70/1.60  #Chain   : 0
% 3.70/1.60  #Close   : 0
% 3.70/1.60  
% 3.70/1.60  Ordering : KBO
% 3.70/1.60  
% 3.70/1.60  Simplification rules
% 3.70/1.60  ----------------------
% 3.70/1.60  #Subsume      : 114
% 3.70/1.60  #Demod        : 559
% 3.70/1.60  #Tautology    : 362
% 3.70/1.60  #SimpNegUnit  : 0
% 3.70/1.61  #BackRed      : 5
% 3.70/1.61  
% 3.70/1.61  #Partial instantiations: 0
% 3.70/1.61  #Strategies tried      : 1
% 3.70/1.61  
% 3.70/1.61  Timing (in seconds)
% 3.70/1.61  ----------------------
% 3.70/1.61  Preprocessing        : 0.28
% 3.70/1.61  Parsing              : 0.16
% 3.70/1.61  CNF conversion       : 0.02
% 3.70/1.61  Main loop            : 0.57
% 3.70/1.61  Inferencing          : 0.19
% 3.70/1.61  Reduction            : 0.21
% 3.70/1.61  Demodulation         : 0.16
% 3.70/1.61  BG Simplification    : 0.02
% 3.70/1.61  Subsumption          : 0.10
% 3.70/1.61  Abstraction          : 0.03
% 3.70/1.61  MUC search           : 0.00
% 3.70/1.61  Cooper               : 0.00
% 3.70/1.61  Total                : 0.88
% 3.70/1.61  Index Insertion      : 0.00
% 3.70/1.61  Index Deletion       : 0.00
% 3.70/1.61  Index Matching       : 0.00
% 3.70/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
