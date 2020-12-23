%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:01 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 109 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 186 expanded)
%              Number of equality atoms :   14 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_58,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_194,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_214,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_194])).

tff(c_382,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_394,plain,(
    ! [C_69] :
      ( ~ r1_xboole_0('#skF_6','#skF_5')
      | ~ r2_hidden(C_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_382])).

tff(c_409,plain,(
    ! [C_69] : ~ r2_hidden(C_69,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_394])).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_62,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_172,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_182,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_172])).

tff(c_301,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),B_62)
      | r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_585,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(k1_tarski(A_88),B_89) = k1_xboole_0
      | r2_hidden(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_301,c_24])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_917,plain,(
    ! [B_100,A_101] :
      ( k3_xboole_0(B_100,k1_tarski(A_101)) = k1_xboole_0
      | r2_hidden(A_101,B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_4])).

tff(c_988,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_917])).

tff(c_3885,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_988])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3904,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_3885,c_8])).

tff(c_2286,plain,(
    ! [D_130,A_131,B_132] :
      ( r2_hidden(D_130,k3_xboole_0(A_131,B_132))
      | ~ r2_hidden(D_130,B_132)
      | ~ r2_hidden(D_130,A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2344,plain,(
    ! [D_130] :
      ( r2_hidden(D_130,k1_xboole_0)
      | ~ r2_hidden(D_130,'#skF_5')
      | ~ r2_hidden(D_130,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_2286])).

tff(c_2364,plain,(
    ! [D_130] :
      ( ~ r2_hidden(D_130,'#skF_5')
      | ~ r2_hidden(D_130,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_2344])).

tff(c_3917,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_3904,c_2364])).

tff(c_3921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3917])).

tff(c_3922,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_988])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_3'(A_15,B_16),k3_xboole_0(A_15,B_16))
      | r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3963,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3922,c_30])).

tff(c_4013,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_3963])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r1_xboole_0(B_14,A_13)
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4046,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4013,c_28])).

tff(c_123,plain,(
    ! [B_47,A_48] :
      ( r1_xboole_0(B_47,A_48)
      | ~ r1_xboole_0(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_129,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_123])).

tff(c_2890,plain,(
    ! [A_139,C_140,B_141] :
      ( ~ r1_xboole_0(A_139,C_140)
      | ~ r1_xboole_0(A_139,B_141)
      | r1_xboole_0(A_139,k2_xboole_0(B_141,C_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_13655,plain,(
    ! [B_271,C_272,A_273] :
      ( r1_xboole_0(k2_xboole_0(B_271,C_272),A_273)
      | ~ r1_xboole_0(A_273,C_272)
      | ~ r1_xboole_0(A_273,B_271) ) ),
    inference(resolution,[status(thm)],[c_2890,c_28])).

tff(c_56,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_13673,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_13655,c_56])).

tff(c_13688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4046,c_129,c_13673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.66/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/2.84  
% 7.66/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/2.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.66/2.85  
% 7.66/2.85  %Foreground sorts:
% 7.66/2.85  
% 7.66/2.85  
% 7.66/2.85  %Background operators:
% 7.66/2.85  
% 7.66/2.85  
% 7.66/2.85  %Foreground operators:
% 7.66/2.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.66/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.66/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.66/2.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.66/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.66/2.85  tff('#skF_7', type, '#skF_7': $i).
% 7.66/2.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.66/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.66/2.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.66/2.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.66/2.85  tff('#skF_5', type, '#skF_5': $i).
% 7.66/2.85  tff('#skF_6', type, '#skF_6': $i).
% 7.66/2.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.66/2.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.66/2.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.66/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.66/2.85  tff('#skF_4', type, '#skF_4': $i).
% 7.66/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.66/2.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.66/2.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.66/2.85  
% 7.66/2.86  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.66/2.86  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.66/2.86  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.66/2.86  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.66/2.86  tff(f_97, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.66/2.86  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.66/2.86  tff(f_38, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.66/2.86  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.66/2.86  tff(f_86, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.66/2.86  tff(c_58, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.66/2.86  tff(c_194, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.66/2.86  tff(c_214, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_194])).
% 7.66/2.86  tff(c_382, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.66/2.86  tff(c_394, plain, (![C_69]: (~r1_xboole_0('#skF_6', '#skF_5') | ~r2_hidden(C_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_214, c_382])).
% 7.66/2.86  tff(c_409, plain, (![C_69]: (~r2_hidden(C_69, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_394])).
% 7.66/2.86  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.66/2.86  tff(c_62, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.66/2.86  tff(c_172, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.66/2.86  tff(c_182, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_172])).
% 7.66/2.86  tff(c_301, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), B_62) | r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.66/2.86  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.66/2.86  tff(c_585, plain, (![A_88, B_89]: (k3_xboole_0(k1_tarski(A_88), B_89)=k1_xboole_0 | r2_hidden(A_88, B_89))), inference(resolution, [status(thm)], [c_301, c_24])).
% 7.66/2.86  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.66/2.86  tff(c_917, plain, (![B_100, A_101]: (k3_xboole_0(B_100, k1_tarski(A_101))=k1_xboole_0 | r2_hidden(A_101, B_100))), inference(superposition, [status(thm), theory('equality')], [c_585, c_4])).
% 7.66/2.86  tff(c_988, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_917])).
% 7.66/2.86  tff(c_3885, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_988])).
% 7.66/2.86  tff(c_8, plain, (![D_10, B_6, A_5]: (r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.66/2.86  tff(c_3904, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_3885, c_8])).
% 7.66/2.86  tff(c_2286, plain, (![D_130, A_131, B_132]: (r2_hidden(D_130, k3_xboole_0(A_131, B_132)) | ~r2_hidden(D_130, B_132) | ~r2_hidden(D_130, A_131))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.66/2.86  tff(c_2344, plain, (![D_130]: (r2_hidden(D_130, k1_xboole_0) | ~r2_hidden(D_130, '#skF_5') | ~r2_hidden(D_130, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_2286])).
% 7.66/2.86  tff(c_2364, plain, (![D_130]: (~r2_hidden(D_130, '#skF_5') | ~r2_hidden(D_130, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_409, c_2344])).
% 7.66/2.86  tff(c_3917, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_3904, c_2364])).
% 7.66/2.86  tff(c_3921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_3917])).
% 7.66/2.86  tff(c_3922, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_988])).
% 7.66/2.86  tff(c_30, plain, (![A_15, B_16]: (r2_hidden('#skF_3'(A_15, B_16), k3_xboole_0(A_15, B_16)) | r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.66/2.86  tff(c_3963, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3922, c_30])).
% 7.66/2.86  tff(c_4013, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_409, c_3963])).
% 7.66/2.86  tff(c_28, plain, (![B_14, A_13]: (r1_xboole_0(B_14, A_13) | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.66/2.86  tff(c_4046, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4013, c_28])).
% 7.66/2.86  tff(c_123, plain, (![B_47, A_48]: (r1_xboole_0(B_47, A_48) | ~r1_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.66/2.86  tff(c_129, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_123])).
% 7.66/2.86  tff(c_2890, plain, (![A_139, C_140, B_141]: (~r1_xboole_0(A_139, C_140) | ~r1_xboole_0(A_139, B_141) | r1_xboole_0(A_139, k2_xboole_0(B_141, C_140)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.66/2.86  tff(c_13655, plain, (![B_271, C_272, A_273]: (r1_xboole_0(k2_xboole_0(B_271, C_272), A_273) | ~r1_xboole_0(A_273, C_272) | ~r1_xboole_0(A_273, B_271))), inference(resolution, [status(thm)], [c_2890, c_28])).
% 7.66/2.86  tff(c_56, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.66/2.86  tff(c_13673, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_13655, c_56])).
% 7.66/2.86  tff(c_13688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4046, c_129, c_13673])).
% 7.66/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/2.86  
% 7.66/2.86  Inference rules
% 7.66/2.86  ----------------------
% 7.66/2.86  #Ref     : 0
% 7.66/2.86  #Sup     : 3290
% 7.66/2.86  #Fact    : 0
% 7.66/2.86  #Define  : 0
% 7.66/2.86  #Split   : 1
% 7.66/2.86  #Chain   : 0
% 7.66/2.86  #Close   : 0
% 7.66/2.86  
% 7.66/2.86  Ordering : KBO
% 7.66/2.86  
% 7.66/2.86  Simplification rules
% 7.66/2.86  ----------------------
% 7.66/2.86  #Subsume      : 271
% 7.66/2.86  #Demod        : 3336
% 7.66/2.86  #Tautology    : 2126
% 7.66/2.86  #SimpNegUnit  : 83
% 7.66/2.86  #BackRed      : 5
% 7.66/2.86  
% 7.66/2.86  #Partial instantiations: 0
% 7.66/2.86  #Strategies tried      : 1
% 7.66/2.86  
% 7.66/2.86  Timing (in seconds)
% 7.66/2.86  ----------------------
% 7.66/2.86  Preprocessing        : 0.38
% 7.66/2.86  Parsing              : 0.19
% 7.66/2.86  CNF conversion       : 0.03
% 7.66/2.86  Main loop            : 1.62
% 7.66/2.86  Inferencing          : 0.39
% 7.66/2.86  Reduction            : 0.84
% 7.66/2.86  Demodulation         : 0.71
% 7.66/2.86  BG Simplification    : 0.05
% 7.66/2.86  Subsumption          : 0.25
% 7.66/2.86  Abstraction          : 0.06
% 7.66/2.86  MUC search           : 0.00
% 7.66/2.86  Cooper               : 0.00
% 7.66/2.86  Total                : 2.03
% 7.66/2.86  Index Insertion      : 0.00
% 7.66/2.86  Index Deletion       : 0.00
% 7.66/2.86  Index Matching       : 0.00
% 7.66/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
