%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:48 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :   60 (  77 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A) )
           => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_127,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_139,plain,(
    ! [A_13,B_14] : k5_xboole_0(k4_xboole_0(A_13,B_14),k1_xboole_0) = k4_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_127])).

tff(c_226,plain,(
    ! [A_51,B_52] : k4_xboole_0(k4_xboole_0(A_51,B_52),B_52) = k4_xboole_0(A_51,B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_139])).

tff(c_241,plain,(
    ! [B_52,A_51] : k5_xboole_0(B_52,k4_xboole_0(A_51,B_52)) = k2_xboole_0(B_52,k4_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_20])).

tff(c_264,plain,(
    ! [B_52,A_51] : k2_xboole_0(B_52,k4_xboole_0(A_51,B_52)) = k2_xboole_0(B_52,A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_241])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_300,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(A_57,B_58) = B_58
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_12])).

tff(c_1749,plain,(
    ! [B_96,A_97] :
      ( k2_xboole_0(k2_relat_1(B_96),A_97) = A_97
      | ~ v5_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_24,c_300])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5303,plain,(
    ! [B_145,C_146,A_147] :
      ( r1_tarski(k2_relat_1(B_145),C_146)
      | ~ r1_tarski(A_147,C_146)
      | ~ v5_relat_1(B_145,A_147)
      | ~ v1_relat_1(B_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_10])).

tff(c_5310,plain,(
    ! [B_148] :
      ( r1_tarski(k2_relat_1(B_148),'#skF_2')
      | ~ v5_relat_1(B_148,'#skF_1')
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_32,c_5303])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( v5_relat_1(B_21,A_20)
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5322,plain,(
    ! [B_149] :
      ( v5_relat_1(B_149,'#skF_2')
      | ~ v5_relat_1(B_149,'#skF_1')
      | ~ v1_relat_1(B_149) ) ),
    inference(resolution,[status(thm)],[c_5310,c_22])).

tff(c_26,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5325,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5322,c_26])).

tff(c_5329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_5325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:07:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.11  
% 5.51/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.12  %$ v5_relat_1 > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.51/2.12  
% 5.51/2.12  %Foreground sorts:
% 5.51/2.12  
% 5.51/2.12  
% 5.51/2.12  %Background operators:
% 5.51/2.12  
% 5.51/2.12  
% 5.51/2.12  %Foreground operators:
% 5.51/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.51/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.51/2.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.51/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.51/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.51/2.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.51/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.51/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.51/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.51/2.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.51/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.51/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.51/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.51/2.12  
% 5.67/2.13  tff(f_65, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t218_relat_1)).
% 5.67/2.13  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.67/2.13  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.67/2.13  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.67/2.13  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.67/2.13  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.67/2.13  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.67/2.13  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 5.67/2.13  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.67/2.13  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.67/2.13  tff(c_28, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.67/2.13  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.67/2.13  tff(c_24, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.67/2.13  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.67/2.13  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.67/2.13  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.67/2.13  tff(c_77, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.13  tff(c_85, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_77])).
% 5.67/2.13  tff(c_127, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.67/2.13  tff(c_139, plain, (![A_13, B_14]: (k5_xboole_0(k4_xboole_0(A_13, B_14), k1_xboole_0)=k4_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(superposition, [status(thm), theory('equality')], [c_85, c_127])).
% 5.67/2.13  tff(c_226, plain, (![A_51, B_52]: (k4_xboole_0(k4_xboole_0(A_51, B_52), B_52)=k4_xboole_0(A_51, B_52))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_139])).
% 5.67/2.13  tff(c_241, plain, (![B_52, A_51]: (k5_xboole_0(B_52, k4_xboole_0(A_51, B_52))=k2_xboole_0(B_52, k4_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_20])).
% 5.67/2.13  tff(c_264, plain, (![B_52, A_51]: (k2_xboole_0(B_52, k4_xboole_0(A_51, B_52))=k2_xboole_0(B_52, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_241])).
% 5.67/2.13  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.67/2.13  tff(c_300, plain, (![A_57, B_58]: (k2_xboole_0(A_57, B_58)=B_58 | ~r1_tarski(A_57, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_12])).
% 5.67/2.13  tff(c_1749, plain, (![B_96, A_97]: (k2_xboole_0(k2_relat_1(B_96), A_97)=A_97 | ~v5_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_24, c_300])).
% 5.67/2.13  tff(c_10, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.67/2.13  tff(c_5303, plain, (![B_145, C_146, A_147]: (r1_tarski(k2_relat_1(B_145), C_146) | ~r1_tarski(A_147, C_146) | ~v5_relat_1(B_145, A_147) | ~v1_relat_1(B_145))), inference(superposition, [status(thm), theory('equality')], [c_1749, c_10])).
% 5.67/2.13  tff(c_5310, plain, (![B_148]: (r1_tarski(k2_relat_1(B_148), '#skF_2') | ~v5_relat_1(B_148, '#skF_1') | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_32, c_5303])).
% 5.67/2.13  tff(c_22, plain, (![B_21, A_20]: (v5_relat_1(B_21, A_20) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.67/2.13  tff(c_5322, plain, (![B_149]: (v5_relat_1(B_149, '#skF_2') | ~v5_relat_1(B_149, '#skF_1') | ~v1_relat_1(B_149))), inference(resolution, [status(thm)], [c_5310, c_22])).
% 5.67/2.13  tff(c_26, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.67/2.13  tff(c_5325, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5322, c_26])).
% 5.67/2.13  tff(c_5329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_5325])).
% 5.67/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.13  
% 5.67/2.13  Inference rules
% 5.67/2.13  ----------------------
% 5.67/2.13  #Ref     : 0
% 5.67/2.13  #Sup     : 1232
% 5.67/2.13  #Fact    : 0
% 5.67/2.13  #Define  : 0
% 5.67/2.13  #Split   : 1
% 5.67/2.13  #Chain   : 0
% 5.67/2.13  #Close   : 0
% 5.67/2.13  
% 5.67/2.13  Ordering : KBO
% 5.67/2.13  
% 5.67/2.13  Simplification rules
% 5.67/2.13  ----------------------
% 5.67/2.13  #Subsume      : 20
% 5.67/2.13  #Demod        : 1541
% 5.67/2.13  #Tautology    : 693
% 5.67/2.13  #SimpNegUnit  : 0
% 5.67/2.13  #BackRed      : 0
% 5.67/2.13  
% 5.67/2.13  #Partial instantiations: 0
% 5.67/2.13  #Strategies tried      : 1
% 5.67/2.13  
% 5.67/2.13  Timing (in seconds)
% 5.67/2.13  ----------------------
% 5.67/2.13  Preprocessing        : 0.29
% 5.67/2.13  Parsing              : 0.16
% 5.67/2.13  CNF conversion       : 0.02
% 5.67/2.13  Main loop            : 1.09
% 5.67/2.13  Inferencing          : 0.33
% 5.67/2.13  Reduction            : 0.51
% 5.67/2.13  Demodulation         : 0.44
% 5.67/2.13  BG Simplification    : 0.06
% 5.67/2.13  Subsumption          : 0.13
% 5.67/2.13  Abstraction          : 0.06
% 5.67/2.13  MUC search           : 0.00
% 5.67/2.13  Cooper               : 0.00
% 5.67/2.13  Total                : 1.40
% 5.67/2.13  Index Insertion      : 0.00
% 5.67/2.13  Index Deletion       : 0.00
% 5.67/2.13  Index Matching       : 0.00
% 5.67/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
