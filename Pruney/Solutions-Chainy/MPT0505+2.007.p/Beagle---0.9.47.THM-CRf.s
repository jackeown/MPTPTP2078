%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:51 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  63 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_43,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_36] : k1_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_177,plain,(
    ! [B_57,A_58] :
      ( k7_relat_1(B_57,A_58) = B_57
      | ~ r1_tarski(k1_relat_1(B_57),A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_180,plain,(
    ! [A_36,A_58] :
      ( k7_relat_1(k6_relat_1(A_36),A_58) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_58)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_177])).

tff(c_226,plain,(
    ! [A_63,A_64] :
      ( k7_relat_1(k6_relat_1(A_63),A_64) = k6_relat_1(A_63)
      | ~ r1_tarski(A_63,A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_180])).

tff(c_183,plain,(
    ! [B_59,A_60] :
      ( k3_xboole_0(k1_relat_1(B_59),A_60) = k1_relat_1(k7_relat_1(B_59,A_60))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_206,plain,(
    ! [A_36,A_60] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_36),A_60)) = k3_xboole_0(A_36,A_60)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_183])).

tff(c_210,plain,(
    ! [A_36,A_60] : k1_relat_1(k7_relat_1(k6_relat_1(A_36),A_60)) = k3_xboole_0(A_36,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_206])).

tff(c_232,plain,(
    ! [A_63,A_64] :
      ( k3_xboole_0(A_63,A_64) = k1_relat_1(k6_relat_1(A_63))
      | ~ r1_tarski(A_63,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_210])).

tff(c_239,plain,(
    ! [A_65,A_66] :
      ( k3_xboole_0(A_65,A_66) = A_65
      | ~ r1_tarski(A_65,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_232])).

tff(c_243,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_239])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [B_50,A_51] : k1_setfam_1(k2_tarski(B_50,A_51)) = k3_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_16,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [B_50,A_51] : k3_xboole_0(B_50,A_51) = k3_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_16])).

tff(c_296,plain,(
    ! [C_73,A_74,B_75] :
      ( k7_relat_1(k7_relat_1(C_73,A_74),B_75) = k7_relat_1(C_73,k3_xboole_0(A_74,B_75))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_305,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_30])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_243,c_117,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:15:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.24  
% 1.95/1.24  %Foreground sorts:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Background operators:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Foreground operators:
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.95/1.25  
% 1.95/1.26  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 1.95/1.26  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.95/1.26  tff(f_43, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.95/1.26  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.95/1.26  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.95/1.26  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.95/1.26  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.95/1.26  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.95/1.26  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.26  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.26  tff(c_22, plain, (![A_36]: (k1_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.26  tff(c_18, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.26  tff(c_177, plain, (![B_57, A_58]: (k7_relat_1(B_57, A_58)=B_57 | ~r1_tarski(k1_relat_1(B_57), A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.26  tff(c_180, plain, (![A_36, A_58]: (k7_relat_1(k6_relat_1(A_36), A_58)=k6_relat_1(A_36) | ~r1_tarski(A_36, A_58) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_177])).
% 1.95/1.26  tff(c_226, plain, (![A_63, A_64]: (k7_relat_1(k6_relat_1(A_63), A_64)=k6_relat_1(A_63) | ~r1_tarski(A_63, A_64))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_180])).
% 1.95/1.26  tff(c_183, plain, (![B_59, A_60]: (k3_xboole_0(k1_relat_1(B_59), A_60)=k1_relat_1(k7_relat_1(B_59, A_60)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.26  tff(c_206, plain, (![A_36, A_60]: (k1_relat_1(k7_relat_1(k6_relat_1(A_36), A_60))=k3_xboole_0(A_36, A_60) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_183])).
% 1.95/1.26  tff(c_210, plain, (![A_36, A_60]: (k1_relat_1(k7_relat_1(k6_relat_1(A_36), A_60))=k3_xboole_0(A_36, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_206])).
% 1.95/1.26  tff(c_232, plain, (![A_63, A_64]: (k3_xboole_0(A_63, A_64)=k1_relat_1(k6_relat_1(A_63)) | ~r1_tarski(A_63, A_64))), inference(superposition, [status(thm), theory('equality')], [c_226, c_210])).
% 1.95/1.26  tff(c_239, plain, (![A_65, A_66]: (k3_xboole_0(A_65, A_66)=A_65 | ~r1_tarski(A_65, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_232])).
% 1.95/1.26  tff(c_243, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_32, c_239])).
% 1.95/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.26  tff(c_87, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.26  tff(c_111, plain, (![B_50, A_51]: (k1_setfam_1(k2_tarski(B_50, A_51))=k3_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87])).
% 1.95/1.26  tff(c_16, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.26  tff(c_117, plain, (![B_50, A_51]: (k3_xboole_0(B_50, A_51)=k3_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_111, c_16])).
% 1.95/1.26  tff(c_296, plain, (![C_73, A_74, B_75]: (k7_relat_1(k7_relat_1(C_73, A_74), B_75)=k7_relat_1(C_73, k3_xboole_0(A_74, B_75)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.26  tff(c_30, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.26  tff(c_305, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_296, c_30])).
% 1.95/1.26  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_243, c_117, c_305])).
% 1.95/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  
% 1.95/1.26  Inference rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Ref     : 0
% 1.95/1.26  #Sup     : 70
% 1.95/1.26  #Fact    : 0
% 1.95/1.26  #Define  : 0
% 1.95/1.26  #Split   : 0
% 1.95/1.26  #Chain   : 0
% 1.95/1.26  #Close   : 0
% 1.95/1.26  
% 1.95/1.26  Ordering : KBO
% 1.95/1.26  
% 1.95/1.26  Simplification rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Subsume      : 9
% 1.95/1.26  #Demod        : 11
% 1.95/1.26  #Tautology    : 44
% 1.95/1.26  #SimpNegUnit  : 0
% 1.95/1.26  #BackRed      : 0
% 1.95/1.26  
% 1.95/1.26  #Partial instantiations: 0
% 1.95/1.26  #Strategies tried      : 1
% 1.95/1.26  
% 1.95/1.26  Timing (in seconds)
% 1.95/1.26  ----------------------
% 1.95/1.26  Preprocessing        : 0.30
% 1.95/1.26  Parsing              : 0.16
% 1.95/1.26  CNF conversion       : 0.02
% 1.95/1.26  Main loop            : 0.17
% 1.95/1.26  Inferencing          : 0.07
% 1.95/1.26  Reduction            : 0.06
% 1.95/1.26  Demodulation         : 0.05
% 1.95/1.26  BG Simplification    : 0.01
% 1.95/1.26  Subsumption          : 0.02
% 1.95/1.26  Abstraction          : 0.01
% 1.95/1.26  MUC search           : 0.00
% 1.95/1.26  Cooper               : 0.00
% 1.95/1.26  Total                : 0.50
% 1.95/1.26  Index Insertion      : 0.00
% 1.95/1.26  Index Deletion       : 0.00
% 1.95/1.26  Index Matching       : 0.00
% 1.95/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
