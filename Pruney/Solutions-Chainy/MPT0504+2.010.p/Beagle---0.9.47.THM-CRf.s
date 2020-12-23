%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:50 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 (  91 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( k3_xboole_0(k1_relat_1(B_17),A_16) = k1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [D_26,B_27,A_28] :
      ( r2_hidden(D_26,B_27)
      | ~ r2_hidden(D_26,k3_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_165,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_55,B_56),B_57),B_56)
      | r1_tarski(k3_xboole_0(A_55,B_56),B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_234,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),B_62) ),
    inference(resolution,[status(thm)],[c_165,c_4])).

tff(c_237,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_234])).

tff(c_36,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_141,plain,(
    ! [A_52,B_53,B_54] :
      ( r2_hidden('#skF_1'(A_52,B_53),B_54)
      | ~ r1_tarski(A_52,B_54)
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_560,plain,(
    ! [A_106,B_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(A_106,B_107),B_108)
      | ~ r1_tarski(B_109,B_108)
      | ~ r1_tarski(A_106,B_109)
      | r1_tarski(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_579,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_1'(A_110,B_111),'#skF_5')
      | ~ r1_tarski(A_110,'#skF_4')
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_36,c_560])).

tff(c_588,plain,(
    ! [A_112] :
      ( ~ r1_tarski(A_112,'#skF_4')
      | r1_tarski(A_112,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_579,c_4])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_639,plain,(
    ! [B_118] :
      ( k7_relat_1(B_118,'#skF_5') = B_118
      | ~ v1_relat_1(B_118)
      | ~ r1_tarski(k1_relat_1(B_118),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_588,c_32])).

tff(c_787,plain,(
    ! [B_136] :
      ( k7_relat_1(k7_relat_1(B_136,'#skF_4'),'#skF_5') = k7_relat_1(B_136,'#skF_4')
      | ~ v1_relat_1(k7_relat_1(B_136,'#skF_4'))
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_237,c_639])).

tff(c_797,plain,(
    ! [A_137] :
      ( k7_relat_1(k7_relat_1(A_137,'#skF_4'),'#skF_5') = k7_relat_1(A_137,'#skF_4')
      | ~ v1_relat_1(A_137) ) ),
    inference(resolution,[status(thm)],[c_28,c_787])).

tff(c_34,plain,(
    k7_relat_1(k7_relat_1('#skF_6','#skF_4'),'#skF_5') != k7_relat_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_818,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_34])).

tff(c_835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.44  
% 2.65/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.44  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.65/1.44  
% 2.65/1.44  %Foreground sorts:
% 2.65/1.44  
% 2.65/1.44  
% 2.65/1.44  %Background operators:
% 2.65/1.44  
% 2.65/1.44  
% 2.65/1.44  %Foreground operators:
% 2.65/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.65/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.65/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.65/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.65/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.65/1.44  
% 2.65/1.45  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 2.65/1.45  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.65/1.45  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.65/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.65/1.45  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.65/1.45  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.65/1.45  tff(c_38, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.65/1.45  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.45  tff(c_30, plain, (![B_17, A_16]: (k3_xboole_0(k1_relat_1(B_17), A_16)=k1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.45  tff(c_50, plain, (![D_26, B_27, A_28]: (r2_hidden(D_26, B_27) | ~r2_hidden(D_26, k3_xboole_0(A_28, B_27)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.45  tff(c_165, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_1'(k3_xboole_0(A_55, B_56), B_57), B_56) | r1_tarski(k3_xboole_0(A_55, B_56), B_57))), inference(resolution, [status(thm)], [c_6, c_50])).
% 2.65/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.45  tff(c_234, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), B_62))), inference(resolution, [status(thm)], [c_165, c_4])).
% 2.65/1.45  tff(c_237, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_30, c_234])).
% 2.65/1.45  tff(c_36, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.65/1.45  tff(c_68, plain, (![C_34, B_35, A_36]: (r2_hidden(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.45  tff(c_141, plain, (![A_52, B_53, B_54]: (r2_hidden('#skF_1'(A_52, B_53), B_54) | ~r1_tarski(A_52, B_54) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.65/1.45  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.45  tff(c_560, plain, (![A_106, B_107, B_108, B_109]: (r2_hidden('#skF_1'(A_106, B_107), B_108) | ~r1_tarski(B_109, B_108) | ~r1_tarski(A_106, B_109) | r1_tarski(A_106, B_107))), inference(resolution, [status(thm)], [c_141, c_2])).
% 2.65/1.45  tff(c_579, plain, (![A_110, B_111]: (r2_hidden('#skF_1'(A_110, B_111), '#skF_5') | ~r1_tarski(A_110, '#skF_4') | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_36, c_560])).
% 2.65/1.45  tff(c_588, plain, (![A_112]: (~r1_tarski(A_112, '#skF_4') | r1_tarski(A_112, '#skF_5'))), inference(resolution, [status(thm)], [c_579, c_4])).
% 2.65/1.45  tff(c_32, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~r1_tarski(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.45  tff(c_639, plain, (![B_118]: (k7_relat_1(B_118, '#skF_5')=B_118 | ~v1_relat_1(B_118) | ~r1_tarski(k1_relat_1(B_118), '#skF_4'))), inference(resolution, [status(thm)], [c_588, c_32])).
% 2.65/1.45  tff(c_787, plain, (![B_136]: (k7_relat_1(k7_relat_1(B_136, '#skF_4'), '#skF_5')=k7_relat_1(B_136, '#skF_4') | ~v1_relat_1(k7_relat_1(B_136, '#skF_4')) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_237, c_639])).
% 2.65/1.45  tff(c_797, plain, (![A_137]: (k7_relat_1(k7_relat_1(A_137, '#skF_4'), '#skF_5')=k7_relat_1(A_137, '#skF_4') | ~v1_relat_1(A_137))), inference(resolution, [status(thm)], [c_28, c_787])).
% 2.65/1.45  tff(c_34, plain, (k7_relat_1(k7_relat_1('#skF_6', '#skF_4'), '#skF_5')!=k7_relat_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.65/1.45  tff(c_818, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_797, c_34])).
% 2.65/1.45  tff(c_835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_818])).
% 2.65/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.45  
% 2.65/1.45  Inference rules
% 2.65/1.45  ----------------------
% 2.65/1.45  #Ref     : 0
% 2.65/1.45  #Sup     : 188
% 2.65/1.45  #Fact    : 0
% 2.65/1.45  #Define  : 0
% 2.65/1.45  #Split   : 1
% 2.65/1.45  #Chain   : 0
% 2.65/1.45  #Close   : 0
% 2.65/1.45  
% 2.65/1.45  Ordering : KBO
% 2.65/1.45  
% 2.65/1.45  Simplification rules
% 2.65/1.45  ----------------------
% 2.65/1.45  #Subsume      : 19
% 2.65/1.45  #Demod        : 7
% 2.65/1.45  #Tautology    : 27
% 2.65/1.45  #SimpNegUnit  : 0
% 2.65/1.45  #BackRed      : 0
% 2.65/1.45  
% 2.65/1.45  #Partial instantiations: 0
% 2.65/1.45  #Strategies tried      : 1
% 2.65/1.45  
% 2.65/1.45  Timing (in seconds)
% 2.65/1.45  ----------------------
% 2.65/1.45  Preprocessing        : 0.30
% 2.65/1.45  Parsing              : 0.15
% 2.65/1.45  CNF conversion       : 0.02
% 2.65/1.45  Main loop            : 0.38
% 2.65/1.45  Inferencing          : 0.14
% 2.65/1.45  Reduction            : 0.09
% 2.65/1.45  Demodulation         : 0.06
% 2.65/1.45  BG Simplification    : 0.02
% 2.65/1.46  Subsumption          : 0.10
% 2.65/1.46  Abstraction          : 0.02
% 2.65/1.46  MUC search           : 0.00
% 2.65/1.46  Cooper               : 0.00
% 2.65/1.46  Total                : 0.71
% 2.65/1.46  Index Insertion      : 0.00
% 2.65/1.46  Index Deletion       : 0.00
% 2.65/1.46  Index Matching       : 0.00
% 2.65/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
