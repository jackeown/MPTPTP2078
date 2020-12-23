%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:23 EST 2020

% Result     : Theorem 17.32s
% Output     : CNFRefutation 17.32s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  95 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_finset_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_finset_1(B)
     => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).

tff(c_30,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_95,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r2_hidden('#skF_1'(A_37,B_38,C_39),C_39)
      | r2_hidden('#skF_2'(A_37,B_38,C_39),C_39)
      | k3_xboole_0(A_37,B_38) = C_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_106,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_2'(A_40,B_41,A_40),A_40)
      | k3_xboole_0(A_40,B_41) = A_40 ) ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_115,plain,(
    ! [A_1,B_2,B_41] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_1,B_2),B_41,k3_xboole_0(A_1,B_2)),A_1)
      | k3_xboole_0(k3_xboole_0(A_1,B_2),B_41) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_106,c_6])).

tff(c_104,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k3_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_74,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden('#skF_1'(A_34,B_35,C_36),A_34)
      | r2_hidden('#skF_2'(A_34,B_35,C_36),C_36)
      | k3_xboole_0(A_34,B_35) = C_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_380,plain,(
    ! [A_74,B_75,A_76,B_77] :
      ( r2_hidden('#skF_2'(A_74,B_75,k3_xboole_0(A_76,B_77)),A_76)
      | r2_hidden('#skF_1'(A_74,B_75,k3_xboole_0(A_76,B_77)),A_74)
      | k3_xboole_0(A_76,B_77) = k3_xboole_0(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_74,c_6])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_909,plain,(
    ! [A_131,A_132,B_133] :
      ( ~ r2_hidden('#skF_2'(A_131,A_132,k3_xboole_0(A_132,B_133)),A_131)
      | r2_hidden('#skF_1'(A_131,A_132,k3_xboole_0(A_132,B_133)),A_131)
      | k3_xboole_0(A_132,B_133) = k3_xboole_0(A_131,A_132) ) ),
    inference(resolution,[status(thm)],[c_380,c_12])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_39447,plain,(
    ! [A_1228,B_1229] :
      ( ~ r2_hidden('#skF_2'(k3_xboole_0(A_1228,B_1229),A_1228,k3_xboole_0(A_1228,B_1229)),A_1228)
      | ~ r2_hidden('#skF_2'(k3_xboole_0(A_1228,B_1229),A_1228,k3_xboole_0(A_1228,B_1229)),k3_xboole_0(A_1228,B_1229))
      | k3_xboole_0(k3_xboole_0(A_1228,B_1229),A_1228) = k3_xboole_0(A_1228,B_1229) ) ),
    inference(resolution,[status(thm)],[c_909,c_8])).

tff(c_39578,plain,(
    ! [B_1230,B_1231] :
      ( ~ r2_hidden('#skF_2'(k3_xboole_0(B_1230,B_1231),B_1230,k3_xboole_0(B_1230,B_1231)),B_1230)
      | k3_xboole_0(k3_xboole_0(B_1230,B_1231),B_1230) = k3_xboole_0(B_1230,B_1231) ) ),
    inference(resolution,[status(thm)],[c_104,c_39447])).

tff(c_39807,plain,(
    ! [B_1232,B_1233] : k3_xboole_0(k3_xboole_0(B_1232,B_1233),B_1232) = k3_xboole_0(B_1232,B_1233) ),
    inference(resolution,[status(thm)],[c_115,c_39578])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( v1_finset_1(k3_xboole_0(A_14,B_15))
      | ~ v1_finset_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42861,plain,(
    ! [B_1234,B_1235] :
      ( v1_finset_1(k3_xboole_0(B_1234,B_1235))
      | ~ v1_finset_1(B_1234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39807,c_26])).

tff(c_28,plain,(
    ~ v1_finset_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42864,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42861,c_28])).

tff(c_42883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.32/9.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.32/9.08  
% 17.32/9.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.32/9.08  %$ r2_hidden > v1_finset_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 17.32/9.08  
% 17.32/9.08  %Foreground sorts:
% 17.32/9.08  
% 17.32/9.08  
% 17.32/9.08  %Background operators:
% 17.32/9.08  
% 17.32/9.08  
% 17.32/9.08  %Foreground operators:
% 17.32/9.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.32/9.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.32/9.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.32/9.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.32/9.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.32/9.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.32/9.08  tff('#skF_3', type, '#skF_3': $i).
% 17.32/9.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.32/9.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.32/9.08  tff('#skF_4', type, '#skF_4': $i).
% 17.32/9.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.32/9.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.32/9.08  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 17.32/9.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.32/9.08  
% 17.32/9.09  tff(f_49, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_finset_1)).
% 17.32/9.09  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 17.32/9.09  tff(f_44, axiom, (![A, B]: (v1_finset_1(B) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_finset_1)).
% 17.32/9.09  tff(c_30, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.32/9.09  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.32/9.09  tff(c_95, plain, (![A_37, B_38, C_39]: (~r2_hidden('#skF_1'(A_37, B_38, C_39), C_39) | r2_hidden('#skF_2'(A_37, B_38, C_39), C_39) | k3_xboole_0(A_37, B_38)=C_39)), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.32/9.09  tff(c_106, plain, (![A_40, B_41]: (r2_hidden('#skF_2'(A_40, B_41, A_40), A_40) | k3_xboole_0(A_40, B_41)=A_40)), inference(resolution, [status(thm)], [c_18, c_95])).
% 17.32/9.09  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.32/9.09  tff(c_115, plain, (![A_1, B_2, B_41]: (r2_hidden('#skF_2'(k3_xboole_0(A_1, B_2), B_41, k3_xboole_0(A_1, B_2)), A_1) | k3_xboole_0(k3_xboole_0(A_1, B_2), B_41)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_106, c_6])).
% 17.32/9.09  tff(c_104, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k3_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_95])).
% 17.32/9.09  tff(c_74, plain, (![A_34, B_35, C_36]: (r2_hidden('#skF_1'(A_34, B_35, C_36), A_34) | r2_hidden('#skF_2'(A_34, B_35, C_36), C_36) | k3_xboole_0(A_34, B_35)=C_36)), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.32/9.09  tff(c_380, plain, (![A_74, B_75, A_76, B_77]: (r2_hidden('#skF_2'(A_74, B_75, k3_xboole_0(A_76, B_77)), A_76) | r2_hidden('#skF_1'(A_74, B_75, k3_xboole_0(A_76, B_77)), A_74) | k3_xboole_0(A_76, B_77)=k3_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_74, c_6])).
% 17.32/9.09  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.32/9.09  tff(c_909, plain, (![A_131, A_132, B_133]: (~r2_hidden('#skF_2'(A_131, A_132, k3_xboole_0(A_132, B_133)), A_131) | r2_hidden('#skF_1'(A_131, A_132, k3_xboole_0(A_132, B_133)), A_131) | k3_xboole_0(A_132, B_133)=k3_xboole_0(A_131, A_132))), inference(resolution, [status(thm)], [c_380, c_12])).
% 17.32/9.09  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.32/9.09  tff(c_39447, plain, (![A_1228, B_1229]: (~r2_hidden('#skF_2'(k3_xboole_0(A_1228, B_1229), A_1228, k3_xboole_0(A_1228, B_1229)), A_1228) | ~r2_hidden('#skF_2'(k3_xboole_0(A_1228, B_1229), A_1228, k3_xboole_0(A_1228, B_1229)), k3_xboole_0(A_1228, B_1229)) | k3_xboole_0(k3_xboole_0(A_1228, B_1229), A_1228)=k3_xboole_0(A_1228, B_1229))), inference(resolution, [status(thm)], [c_909, c_8])).
% 17.32/9.09  tff(c_39578, plain, (![B_1230, B_1231]: (~r2_hidden('#skF_2'(k3_xboole_0(B_1230, B_1231), B_1230, k3_xboole_0(B_1230, B_1231)), B_1230) | k3_xboole_0(k3_xboole_0(B_1230, B_1231), B_1230)=k3_xboole_0(B_1230, B_1231))), inference(resolution, [status(thm)], [c_104, c_39447])).
% 17.32/9.09  tff(c_39807, plain, (![B_1232, B_1233]: (k3_xboole_0(k3_xboole_0(B_1232, B_1233), B_1232)=k3_xboole_0(B_1232, B_1233))), inference(resolution, [status(thm)], [c_115, c_39578])).
% 17.32/9.09  tff(c_26, plain, (![A_14, B_15]: (v1_finset_1(k3_xboole_0(A_14, B_15)) | ~v1_finset_1(B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 17.32/9.09  tff(c_42861, plain, (![B_1234, B_1235]: (v1_finset_1(k3_xboole_0(B_1234, B_1235)) | ~v1_finset_1(B_1234))), inference(superposition, [status(thm), theory('equality')], [c_39807, c_26])).
% 17.32/9.09  tff(c_28, plain, (~v1_finset_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.32/9.09  tff(c_42864, plain, (~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_42861, c_28])).
% 17.32/9.09  tff(c_42883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_42864])).
% 17.32/9.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.32/9.09  
% 17.32/9.09  Inference rules
% 17.32/9.09  ----------------------
% 17.32/9.09  #Ref     : 0
% 17.32/9.09  #Sup     : 9228
% 17.32/9.09  #Fact    : 0
% 17.32/9.09  #Define  : 0
% 17.32/9.09  #Split   : 0
% 17.32/9.09  #Chain   : 0
% 17.32/9.09  #Close   : 0
% 17.32/9.09  
% 17.32/9.09  Ordering : KBO
% 17.32/9.09  
% 17.32/9.09  Simplification rules
% 17.32/9.09  ----------------------
% 17.32/9.09  #Subsume      : 5048
% 17.32/9.09  #Demod        : 20066
% 17.32/9.09  #Tautology    : 1819
% 17.32/9.09  #SimpNegUnit  : 0
% 17.32/9.09  #BackRed      : 19
% 17.32/9.09  
% 17.32/9.09  #Partial instantiations: 0
% 17.32/9.09  #Strategies tried      : 1
% 17.32/9.09  
% 17.32/9.09  Timing (in seconds)
% 17.32/9.09  ----------------------
% 17.32/9.09  Preprocessing        : 0.31
% 17.32/9.09  Parsing              : 0.16
% 17.32/9.09  CNF conversion       : 0.02
% 17.32/9.09  Main loop            : 7.99
% 17.32/9.09  Inferencing          : 2.02
% 17.32/9.09  Reduction            : 1.91
% 17.32/9.09  Demodulation         : 1.47
% 17.32/9.09  BG Simplification    : 0.16
% 17.32/9.09  Subsumption          : 3.60
% 17.32/9.09  Abstraction          : 0.54
% 17.32/9.09  MUC search           : 0.00
% 17.32/9.09  Cooper               : 0.00
% 17.32/9.09  Total                : 8.32
% 17.32/9.09  Index Insertion      : 0.00
% 17.32/9.09  Index Deletion       : 0.00
% 17.32/9.09  Index Matching       : 0.00
% 17.32/9.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
