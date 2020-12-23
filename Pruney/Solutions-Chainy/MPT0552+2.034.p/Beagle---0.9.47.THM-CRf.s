%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:01 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 128 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_27,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [B_28,A_29] : r1_tarski(k3_xboole_0(B_28,A_29),A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_4])).

tff(c_18,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [C_19,B_18,A_17] :
      ( k7_relat_1(k7_relat_1(C_19,B_18),A_17) = k7_relat_1(C_19,A_17)
      | ~ r1_tarski(A_17,B_18)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_112,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_41,A_42)),k2_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_158,plain,(
    ! [B_51,A_52,A_53] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_51,A_52),A_53)),k9_relat_1(B_51,A_52))
      | ~ v1_relat_1(k7_relat_1(B_51,A_52))
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_1262,plain,(
    ! [C_158,A_159,B_160] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_158,A_159)),k9_relat_1(C_158,B_160))
      | ~ v1_relat_1(k7_relat_1(C_158,B_160))
      | ~ v1_relat_1(C_158)
      | ~ r1_tarski(A_159,B_160)
      | ~ v1_relat_1(C_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_158])).

tff(c_1282,plain,(
    ! [B_164,A_165,B_166] :
      ( r1_tarski(k9_relat_1(B_164,A_165),k9_relat_1(B_164,B_166))
      | ~ v1_relat_1(k7_relat_1(B_164,B_166))
      | ~ v1_relat_1(B_164)
      | ~ r1_tarski(A_165,B_166)
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1262])).

tff(c_134,plain,(
    ! [C_48,B_49,A_50] :
      ( k7_relat_1(k7_relat_1(C_48,B_49),A_50) = k7_relat_1(C_48,A_50)
      | ~ r1_tarski(A_50,B_49)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_23,A_22)),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_193,plain,(
    ! [C_60,A_61,B_62] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_60,A_61)),k2_relat_1(k7_relat_1(C_60,B_62)))
      | ~ v1_relat_1(k7_relat_1(C_60,B_62))
      | ~ r1_tarski(A_61,B_62)
      | ~ v1_relat_1(C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_20])).

tff(c_227,plain,(
    ! [B_69,A_70,A_71] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_69,A_70)),k9_relat_1(B_69,A_71))
      | ~ v1_relat_1(k7_relat_1(B_69,A_71))
      | ~ r1_tarski(A_70,A_71)
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_193])).

tff(c_1165,plain,(
    ! [B_148,A_149,A_150] :
      ( r1_tarski(k9_relat_1(B_148,A_149),k9_relat_1(B_148,A_150))
      | ~ v1_relat_1(k7_relat_1(B_148,A_150))
      | ~ r1_tarski(A_149,A_150)
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_227])).

tff(c_123,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(A_45,k3_xboole_0(B_46,C_47))
      | ~ r1_tarski(A_45,C_47)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_133,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_123,c_22])).

tff(c_206,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_1172,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1165,c_206])).

tff(c_1183,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4,c_1172])).

tff(c_1245,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1183])).

tff(c_1249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1245])).

tff(c_1250,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_1285,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1282,c_1250])).

tff(c_1294,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42,c_1285])).

tff(c_1303,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1294])).

tff(c_1307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.64  
% 3.40/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.64  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.40/1.64  
% 3.40/1.64  %Foreground sorts:
% 3.40/1.64  
% 3.40/1.64  
% 3.40/1.64  %Background operators:
% 3.40/1.64  
% 3.40/1.64  
% 3.40/1.64  %Foreground operators:
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.40/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.40/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.40/1.64  
% 3.73/1.65  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 3.73/1.65  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.73/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.73/1.65  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.73/1.65  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.73/1.65  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 3.73/1.65  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 3.73/1.65  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.73/1.65  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.73/1.65  tff(c_14, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.73/1.65  tff(c_27, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.73/1.65  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.73/1.65  tff(c_42, plain, (![B_28, A_29]: (r1_tarski(k3_xboole_0(B_28, A_29), A_29))), inference(superposition, [status(thm), theory('equality')], [c_27, c_4])).
% 3.73/1.65  tff(c_18, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.73/1.65  tff(c_16, plain, (![C_19, B_18, A_17]: (k7_relat_1(k7_relat_1(C_19, B_18), A_17)=k7_relat_1(C_19, A_17) | ~r1_tarski(A_17, B_18) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.73/1.65  tff(c_112, plain, (![B_41, A_42]: (r1_tarski(k2_relat_1(k7_relat_1(B_41, A_42)), k2_relat_1(B_41)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.73/1.65  tff(c_158, plain, (![B_51, A_52, A_53]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_51, A_52), A_53)), k9_relat_1(B_51, A_52)) | ~v1_relat_1(k7_relat_1(B_51, A_52)) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_18, c_112])).
% 3.73/1.65  tff(c_1262, plain, (![C_158, A_159, B_160]: (r1_tarski(k2_relat_1(k7_relat_1(C_158, A_159)), k9_relat_1(C_158, B_160)) | ~v1_relat_1(k7_relat_1(C_158, B_160)) | ~v1_relat_1(C_158) | ~r1_tarski(A_159, B_160) | ~v1_relat_1(C_158))), inference(superposition, [status(thm), theory('equality')], [c_16, c_158])).
% 3.73/1.65  tff(c_1282, plain, (![B_164, A_165, B_166]: (r1_tarski(k9_relat_1(B_164, A_165), k9_relat_1(B_164, B_166)) | ~v1_relat_1(k7_relat_1(B_164, B_166)) | ~v1_relat_1(B_164) | ~r1_tarski(A_165, B_166) | ~v1_relat_1(B_164) | ~v1_relat_1(B_164))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1262])).
% 3.73/1.65  tff(c_134, plain, (![C_48, B_49, A_50]: (k7_relat_1(k7_relat_1(C_48, B_49), A_50)=k7_relat_1(C_48, A_50) | ~r1_tarski(A_50, B_49) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.73/1.65  tff(c_20, plain, (![B_23, A_22]: (r1_tarski(k2_relat_1(k7_relat_1(B_23, A_22)), k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.73/1.65  tff(c_193, plain, (![C_60, A_61, B_62]: (r1_tarski(k2_relat_1(k7_relat_1(C_60, A_61)), k2_relat_1(k7_relat_1(C_60, B_62))) | ~v1_relat_1(k7_relat_1(C_60, B_62)) | ~r1_tarski(A_61, B_62) | ~v1_relat_1(C_60))), inference(superposition, [status(thm), theory('equality')], [c_134, c_20])).
% 3.73/1.65  tff(c_227, plain, (![B_69, A_70, A_71]: (r1_tarski(k2_relat_1(k7_relat_1(B_69, A_70)), k9_relat_1(B_69, A_71)) | ~v1_relat_1(k7_relat_1(B_69, A_71)) | ~r1_tarski(A_70, A_71) | ~v1_relat_1(B_69) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_18, c_193])).
% 3.73/1.65  tff(c_1165, plain, (![B_148, A_149, A_150]: (r1_tarski(k9_relat_1(B_148, A_149), k9_relat_1(B_148, A_150)) | ~v1_relat_1(k7_relat_1(B_148, A_150)) | ~r1_tarski(A_149, A_150) | ~v1_relat_1(B_148) | ~v1_relat_1(B_148) | ~v1_relat_1(B_148))), inference(superposition, [status(thm), theory('equality')], [c_18, c_227])).
% 3.73/1.65  tff(c_123, plain, (![A_45, B_46, C_47]: (r1_tarski(A_45, k3_xboole_0(B_46, C_47)) | ~r1_tarski(A_45, C_47) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.73/1.65  tff(c_22, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.73/1.65  tff(c_133, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_123, c_22])).
% 3.73/1.65  tff(c_206, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_133])).
% 3.73/1.65  tff(c_1172, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1165, c_206])).
% 3.73/1.65  tff(c_1183, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4, c_1172])).
% 3.73/1.65  tff(c_1245, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1183])).
% 3.73/1.65  tff(c_1249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1245])).
% 3.73/1.65  tff(c_1250, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_133])).
% 3.73/1.65  tff(c_1285, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1282, c_1250])).
% 3.73/1.65  tff(c_1294, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_42, c_1285])).
% 3.73/1.65  tff(c_1303, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1294])).
% 3.73/1.65  tff(c_1307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1303])).
% 3.73/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.65  
% 3.73/1.65  Inference rules
% 3.73/1.65  ----------------------
% 3.73/1.65  #Ref     : 0
% 3.73/1.65  #Sup     : 370
% 3.73/1.65  #Fact    : 0
% 3.73/1.65  #Define  : 0
% 3.73/1.65  #Split   : 1
% 3.73/1.65  #Chain   : 0
% 3.73/1.66  #Close   : 0
% 3.73/1.66  
% 3.73/1.66  Ordering : KBO
% 3.73/1.66  
% 3.73/1.66  Simplification rules
% 3.73/1.66  ----------------------
% 3.73/1.66  #Subsume      : 90
% 3.73/1.66  #Demod        : 9
% 3.73/1.66  #Tautology    : 35
% 3.73/1.66  #SimpNegUnit  : 0
% 3.73/1.66  #BackRed      : 0
% 3.73/1.66  
% 3.73/1.66  #Partial instantiations: 0
% 3.73/1.66  #Strategies tried      : 1
% 3.73/1.66  
% 3.73/1.66  Timing (in seconds)
% 3.73/1.66  ----------------------
% 3.73/1.66  Preprocessing        : 0.29
% 3.73/1.66  Parsing              : 0.16
% 3.73/1.66  CNF conversion       : 0.02
% 3.73/1.66  Main loop            : 0.54
% 3.73/1.66  Inferencing          : 0.20
% 3.73/1.66  Reduction            : 0.16
% 3.73/1.66  Demodulation         : 0.13
% 3.73/1.66  BG Simplification    : 0.03
% 3.73/1.66  Subsumption          : 0.11
% 3.73/1.66  Abstraction          : 0.03
% 3.73/1.66  MUC search           : 0.00
% 3.73/1.66  Cooper               : 0.00
% 3.73/1.66  Total                : 0.85
% 3.73/1.66  Index Insertion      : 0.00
% 3.73/1.66  Index Deletion       : 0.00
% 3.73/1.66  Index Matching       : 0.00
% 3.73/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
