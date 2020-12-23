%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:11 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 162 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 274 expanded)
%              Number of equality atoms :   24 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_57,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_795,plain,(
    ! [A_131,C_132,B_133] :
      ( ~ r1_xboole_0(A_131,C_132)
      | ~ r1_xboole_0(A_131,B_133)
      | r1_xboole_0(A_131,k2_xboole_0(B_133,C_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3577,plain,(
    ! [B_232,C_233,A_234] :
      ( r1_xboole_0(k2_xboole_0(B_232,C_233),A_234)
      | ~ r1_xboole_0(A_234,C_233)
      | ~ r1_xboole_0(A_234,B_232) ) ),
    inference(resolution,[status(thm)],[c_795,c_4])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3606,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_3577,c_40])).

tff(c_3617,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3606])).

tff(c_3633,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_3617])).

tff(c_44,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_583,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ r1_xboole_0(A_115,B_116)
      | ~ r2_hidden(C_117,B_116)
      | ~ r2_hidden(C_117,A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_647,plain,(
    ! [C_118] :
      ( ~ r2_hidden(C_118,'#skF_4')
      | ~ r2_hidden(C_118,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_583])).

tff(c_661,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_647])).

tff(c_115,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(k1_tarski(A_45),B_46)
      | r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_118,plain,(
    ! [B_46,A_45] :
      ( r1_xboole_0(B_46,k1_tarski(A_45))
      | r2_hidden(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_203,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_xboole_0(A_62,k4_xboole_0(C_63,B_64))
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1076,plain,(
    ! [A_164,C_165,B_166] :
      ( k4_xboole_0(A_164,k4_xboole_0(C_165,B_166)) = A_164
      | ~ r1_tarski(A_164,B_166) ) ),
    inference(resolution,[status(thm)],[c_203,c_26])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1153,plain,(
    ! [C_167,B_168] :
      ( k3_xboole_0(C_167,B_168) = C_167
      | ~ r1_tarski(C_167,B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_16])).

tff(c_1157,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_1153])).

tff(c_237,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | r1_xboole_0(A_67,k3_xboole_0(B_68,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_365,plain,(
    ! [B_85,C_86,A_87] :
      ( r1_xboole_0(k3_xboole_0(B_85,C_86),A_87)
      | ~ r1_xboole_0(A_87,B_85) ) ),
    inference(resolution,[status(thm)],[c_237,c_4])).

tff(c_381,plain,(
    ! [B_2,A_1,A_87] :
      ( r1_xboole_0(k3_xboole_0(B_2,A_1),A_87)
      | ~ r1_xboole_0(A_87,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_365])).

tff(c_2697,plain,(
    ! [A_206] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_206)
      | ~ r1_xboole_0(A_206,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_381])).

tff(c_2747,plain,(
    ! [B_46] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_46)
      | r2_hidden('#skF_6',B_46) ) ),
    inference(resolution,[status(thm)],[c_118,c_2697])).

tff(c_697,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_2'(A_123,B_124),k3_xboole_0(A_123,B_124))
      | r1_xboole_0(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_706,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2),k3_xboole_0(B_2,A_1))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_697])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | r1_xboole_0(A_20,k3_xboole_0(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3507,plain,(
    ! [C_224,B_225,C_226,A_227] :
      ( ~ r2_hidden(C_224,k3_xboole_0(B_225,C_226))
      | ~ r2_hidden(C_224,A_227)
      | ~ r1_xboole_0(A_227,B_225) ) ),
    inference(resolution,[status(thm)],[c_24,c_583])).

tff(c_7119,plain,(
    ! [A_369,B_370,A_371] :
      ( ~ r2_hidden('#skF_2'(A_369,B_370),A_371)
      | ~ r1_xboole_0(A_371,B_370)
      | r1_xboole_0(A_369,B_370) ) ),
    inference(resolution,[status(thm)],[c_706,c_3507])).

tff(c_7158,plain,(
    ! [B_372,A_373] :
      ( ~ r1_xboole_0(k3_xboole_0(B_372,A_373),B_372)
      | r1_xboole_0(A_373,B_372) ) ),
    inference(resolution,[status(thm)],[c_706,c_7119])).

tff(c_7199,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_2747,c_7158])).

tff(c_7333,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_7199])).

tff(c_839,plain,(
    ! [A_150,B_151,C_152] :
      ( k4_xboole_0(A_150,k3_xboole_0(B_151,C_152)) = A_150
      | ~ r1_xboole_0(A_150,B_151) ) ),
    inference(resolution,[status(thm)],[c_237,c_26])).

tff(c_1278,plain,(
    ! [A_173,A_174,B_175] :
      ( k4_xboole_0(A_173,k3_xboole_0(A_174,B_175)) = A_173
      | ~ r1_xboole_0(A_173,B_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_839])).

tff(c_119,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = A_47
      | ~ r1_xboole_0(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_134,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_119])).

tff(c_291,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k4_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_309,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_291])).

tff(c_329,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_16])).

tff(c_1297,plain,
    ( k3_xboole_0('#skF_4','#skF_4') = '#skF_4'
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_329])).

tff(c_1344,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1297])).

tff(c_5295,plain,(
    ! [B_331,C_332,A_333] :
      ( k4_xboole_0(k3_xboole_0(B_331,C_332),A_333) = k3_xboole_0(B_331,C_332)
      | ~ r1_xboole_0(A_333,B_331) ) ),
    inference(resolution,[status(thm)],[c_365,c_26])).

tff(c_5465,plain,(
    ! [A_333] :
      ( k4_xboole_0('#skF_4',A_333) = k3_xboole_0('#skF_4','#skF_4')
      | ~ r1_xboole_0(A_333,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1344,c_5295])).

tff(c_5534,plain,(
    ! [A_333] :
      ( k4_xboole_0('#skF_4',A_333) = '#skF_4'
      | ~ r1_xboole_0(A_333,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_5465])).

tff(c_7362,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7333,c_5534])).

tff(c_7373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3633,c_7362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:52:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.32/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/2.56  
% 7.32/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/2.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.32/2.57  
% 7.32/2.57  %Foreground sorts:
% 7.32/2.57  
% 7.32/2.57  
% 7.32/2.57  %Background operators:
% 7.32/2.57  
% 7.32/2.57  
% 7.32/2.57  %Foreground operators:
% 7.32/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.32/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.32/2.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.32/2.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.32/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.32/2.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.32/2.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.32/2.57  tff('#skF_5', type, '#skF_5': $i).
% 7.32/2.57  tff('#skF_6', type, '#skF_6': $i).
% 7.32/2.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.32/2.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.32/2.57  tff('#skF_3', type, '#skF_3': $i).
% 7.32/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.32/2.57  tff('#skF_4', type, '#skF_4': $i).
% 7.32/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.32/2.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.32/2.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.32/2.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.32/2.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.32/2.57  
% 7.32/2.58  tff(f_91, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.32/2.58  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.32/2.58  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.32/2.58  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.32/2.58  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.32/2.58  tff(f_106, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.32/2.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.32/2.58  tff(f_95, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 7.32/2.58  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.32/2.58  tff(f_87, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 7.32/2.58  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.32/2.58  tff(c_28, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k4_xboole_0(A_23, B_24)!=A_23)), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.32/2.58  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.32/2.58  tff(c_57, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.32/2.58  tff(c_60, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_57])).
% 7.32/2.58  tff(c_795, plain, (![A_131, C_132, B_133]: (~r1_xboole_0(A_131, C_132) | ~r1_xboole_0(A_131, B_133) | r1_xboole_0(A_131, k2_xboole_0(B_133, C_132)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.32/2.58  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.32/2.58  tff(c_3577, plain, (![B_232, C_233, A_234]: (r1_xboole_0(k2_xboole_0(B_232, C_233), A_234) | ~r1_xboole_0(A_234, C_233) | ~r1_xboole_0(A_234, B_232))), inference(resolution, [status(thm)], [c_795, c_4])).
% 7.32/2.58  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.32/2.58  tff(c_3606, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_3577, c_40])).
% 7.32/2.58  tff(c_3617, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3606])).
% 7.32/2.58  tff(c_3633, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_28, c_3617])).
% 7.32/2.58  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.32/2.58  tff(c_583, plain, (![A_115, B_116, C_117]: (~r1_xboole_0(A_115, B_116) | ~r2_hidden(C_117, B_116) | ~r2_hidden(C_117, A_115))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.32/2.58  tff(c_647, plain, (![C_118]: (~r2_hidden(C_118, '#skF_4') | ~r2_hidden(C_118, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_583])).
% 7.32/2.58  tff(c_661, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_647])).
% 7.32/2.58  tff(c_115, plain, (![A_45, B_46]: (r1_xboole_0(k1_tarski(A_45), B_46) | r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.32/2.58  tff(c_118, plain, (![B_46, A_45]: (r1_xboole_0(B_46, k1_tarski(A_45)) | r2_hidden(A_45, B_46))), inference(resolution, [status(thm)], [c_115, c_4])).
% 7.32/2.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.32/2.58  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.32/2.58  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 7.32/2.58  tff(c_203, plain, (![A_62, C_63, B_64]: (r1_xboole_0(A_62, k4_xboole_0(C_63, B_64)) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.32/2.58  tff(c_26, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.32/2.58  tff(c_1076, plain, (![A_164, C_165, B_166]: (k4_xboole_0(A_164, k4_xboole_0(C_165, B_166))=A_164 | ~r1_tarski(A_164, B_166))), inference(resolution, [status(thm)], [c_203, c_26])).
% 7.32/2.58  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.32/2.58  tff(c_1153, plain, (![C_167, B_168]: (k3_xboole_0(C_167, B_168)=C_167 | ~r1_tarski(C_167, B_168))), inference(superposition, [status(thm), theory('equality')], [c_1076, c_16])).
% 7.32/2.58  tff(c_1157, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_47, c_1153])).
% 7.32/2.58  tff(c_237, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | r1_xboole_0(A_67, k3_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.32/2.58  tff(c_365, plain, (![B_85, C_86, A_87]: (r1_xboole_0(k3_xboole_0(B_85, C_86), A_87) | ~r1_xboole_0(A_87, B_85))), inference(resolution, [status(thm)], [c_237, c_4])).
% 7.32/2.58  tff(c_381, plain, (![B_2, A_1, A_87]: (r1_xboole_0(k3_xboole_0(B_2, A_1), A_87) | ~r1_xboole_0(A_87, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_365])).
% 7.32/2.58  tff(c_2697, plain, (![A_206]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_206) | ~r1_xboole_0(A_206, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1157, c_381])).
% 7.32/2.58  tff(c_2747, plain, (![B_46]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_46) | r2_hidden('#skF_6', B_46))), inference(resolution, [status(thm)], [c_118, c_2697])).
% 7.32/2.58  tff(c_697, plain, (![A_123, B_124]: (r2_hidden('#skF_2'(A_123, B_124), k3_xboole_0(A_123, B_124)) | r1_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.32/2.58  tff(c_706, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2), k3_xboole_0(B_2, A_1)) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_697])).
% 7.32/2.58  tff(c_24, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | r1_xboole_0(A_20, k3_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.32/2.58  tff(c_3507, plain, (![C_224, B_225, C_226, A_227]: (~r2_hidden(C_224, k3_xboole_0(B_225, C_226)) | ~r2_hidden(C_224, A_227) | ~r1_xboole_0(A_227, B_225))), inference(resolution, [status(thm)], [c_24, c_583])).
% 7.32/2.58  tff(c_7119, plain, (![A_369, B_370, A_371]: (~r2_hidden('#skF_2'(A_369, B_370), A_371) | ~r1_xboole_0(A_371, B_370) | r1_xboole_0(A_369, B_370))), inference(resolution, [status(thm)], [c_706, c_3507])).
% 7.32/2.58  tff(c_7158, plain, (![B_372, A_373]: (~r1_xboole_0(k3_xboole_0(B_372, A_373), B_372) | r1_xboole_0(A_373, B_372))), inference(resolution, [status(thm)], [c_706, c_7119])).
% 7.32/2.58  tff(c_7199, plain, (r1_xboole_0('#skF_3', '#skF_4') | r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_2747, c_7158])).
% 7.32/2.58  tff(c_7333, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_661, c_7199])).
% 7.32/2.58  tff(c_839, plain, (![A_150, B_151, C_152]: (k4_xboole_0(A_150, k3_xboole_0(B_151, C_152))=A_150 | ~r1_xboole_0(A_150, B_151))), inference(resolution, [status(thm)], [c_237, c_26])).
% 7.32/2.58  tff(c_1278, plain, (![A_173, A_174, B_175]: (k4_xboole_0(A_173, k3_xboole_0(A_174, B_175))=A_173 | ~r1_xboole_0(A_173, B_175))), inference(superposition, [status(thm), theory('equality')], [c_2, c_839])).
% 7.32/2.58  tff(c_119, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=A_47 | ~r1_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.32/2.58  tff(c_134, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_119])).
% 7.32/2.58  tff(c_291, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k4_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.32/2.58  tff(c_309, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_134, c_291])).
% 7.32/2.58  tff(c_329, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_309, c_16])).
% 7.32/2.58  tff(c_1297, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4' | ~r1_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1278, c_329])).
% 7.32/2.58  tff(c_1344, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1297])).
% 7.32/2.58  tff(c_5295, plain, (![B_331, C_332, A_333]: (k4_xboole_0(k3_xboole_0(B_331, C_332), A_333)=k3_xboole_0(B_331, C_332) | ~r1_xboole_0(A_333, B_331))), inference(resolution, [status(thm)], [c_365, c_26])).
% 7.32/2.58  tff(c_5465, plain, (![A_333]: (k4_xboole_0('#skF_4', A_333)=k3_xboole_0('#skF_4', '#skF_4') | ~r1_xboole_0(A_333, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1344, c_5295])).
% 7.32/2.58  tff(c_5534, plain, (![A_333]: (k4_xboole_0('#skF_4', A_333)='#skF_4' | ~r1_xboole_0(A_333, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1344, c_5465])).
% 7.32/2.58  tff(c_7362, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_7333, c_5534])).
% 7.32/2.58  tff(c_7373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3633, c_7362])).
% 7.32/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/2.58  
% 7.32/2.58  Inference rules
% 7.32/2.58  ----------------------
% 7.32/2.58  #Ref     : 0
% 7.32/2.58  #Sup     : 1855
% 7.32/2.58  #Fact    : 0
% 7.32/2.58  #Define  : 0
% 7.32/2.58  #Split   : 12
% 7.32/2.58  #Chain   : 0
% 7.32/2.58  #Close   : 0
% 7.32/2.58  
% 7.32/2.58  Ordering : KBO
% 7.32/2.58  
% 7.32/2.58  Simplification rules
% 7.32/2.58  ----------------------
% 7.32/2.58  #Subsume      : 504
% 7.32/2.58  #Demod        : 297
% 7.32/2.58  #Tautology    : 285
% 7.32/2.58  #SimpNegUnit  : 144
% 7.32/2.58  #BackRed      : 67
% 7.32/2.58  
% 7.32/2.58  #Partial instantiations: 0
% 7.32/2.58  #Strategies tried      : 1
% 7.32/2.58  
% 7.32/2.58  Timing (in seconds)
% 7.32/2.58  ----------------------
% 7.32/2.58  Preprocessing        : 0.30
% 7.32/2.58  Parsing              : 0.16
% 7.32/2.58  CNF conversion       : 0.02
% 7.32/2.58  Main loop            : 1.45
% 7.32/2.58  Inferencing          : 0.44
% 7.32/2.58  Reduction            : 0.45
% 7.32/2.58  Demodulation         : 0.31
% 7.32/2.58  BG Simplification    : 0.05
% 7.32/2.58  Subsumption          : 0.40
% 7.32/2.58  Abstraction          : 0.06
% 7.32/2.58  MUC search           : 0.00
% 7.32/2.58  Cooper               : 0.00
% 7.32/2.58  Total                : 1.79
% 7.32/2.59  Index Insertion      : 0.00
% 7.32/2.59  Index Deletion       : 0.00
% 7.32/2.59  Index Matching       : 0.00
% 7.32/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
