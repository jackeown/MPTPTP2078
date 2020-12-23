%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:06 EST 2020

% Result     : Theorem 12.21s
% Output     : CNFRefutation 12.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 116 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 188 expanded)
%              Number of equality atoms :   12 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_106,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | ~ r1_xboole_0(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_106])).

tff(c_1081,plain,(
    ! [A_137,C_138,B_139] :
      ( ~ r1_xboole_0(A_137,C_138)
      | ~ r1_xboole_0(A_137,B_139)
      | r1_xboole_0(A_137,k2_xboole_0(B_139,C_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5969,plain,(
    ! [B_328,C_329,A_330] :
      ( r1_xboole_0(k2_xboole_0(B_328,C_329),A_330)
      | ~ r1_xboole_0(A_330,C_329)
      | ~ r1_xboole_0(A_330,B_328) ) ),
    inference(resolution,[status(thm)],[c_1081,c_22])).

tff(c_56,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6003,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5969,c_56])).

tff(c_6016,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_6003])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_735,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_3'(A_118,B_119),k3_xboole_0(A_118,B_119))
      | r1_xboole_0(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_744,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_3'(A_1,B_2),k3_xboole_0(B_2,A_1))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_735])).

tff(c_62,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_194,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2673,plain,(
    ! [A_232,B_233] :
      ( k4_xboole_0(k1_tarski(A_232),B_233) = k1_tarski(A_232)
      | r2_hidden(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_194,c_44])).

tff(c_28,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_xboole_0(A_16,C_18)
      | ~ r1_tarski(A_16,k4_xboole_0(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_15054,plain,(
    ! [A_618,B_619,A_620] :
      ( r1_xboole_0(A_618,B_619)
      | ~ r1_tarski(A_618,k1_tarski(A_620))
      | r2_hidden(A_620,B_619) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2673,c_28])).

tff(c_15058,plain,(
    ! [B_621] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),B_621)
      | r2_hidden('#skF_7',B_621) ) ),
    inference(resolution,[status(thm)],[c_62,c_15054])).

tff(c_452,plain,(
    ! [A_106,B_107] : k4_xboole_0(A_106,k4_xboole_0(A_106,B_107)) = k3_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [A_27,B_28] : r1_xboole_0(k4_xboole_0(A_27,B_28),B_28) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_146,plain,(
    ! [B_48,A_49] : r1_xboole_0(B_48,k4_xboole_0(A_49,B_48)) ),
    inference(resolution,[status(thm)],[c_42,c_106])).

tff(c_158,plain,(
    ! [B_48,A_49] : k4_xboole_0(B_48,k4_xboole_0(A_49,B_48)) = B_48 ),
    inference(resolution,[status(thm)],[c_146,c_44])).

tff(c_516,plain,(
    ! [B_111] : k3_xboole_0(B_111,B_111) = B_111 ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_158])).

tff(c_26,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,k3_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_525,plain,(
    ! [B_111,C_15] :
      ( ~ r1_xboole_0(B_111,B_111)
      | ~ r2_hidden(C_15,B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_26])).

tff(c_15130,plain,(
    ! [C_15] :
      ( ~ r2_hidden(C_15,k3_xboole_0('#skF_4','#skF_5'))
      | r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_15058,c_525])).

tff(c_23359,plain,(
    ! [C_780] : ~ r2_hidden(C_780,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_15130])).

tff(c_23407,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_744,c_23359])).

tff(c_23454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6016,c_23407])).

tff(c_23455,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_15130])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1454,plain,(
    ! [D_166,A_167,B_168] :
      ( r2_hidden(D_166,A_167)
      | ~ r2_hidden(D_166,k3_xboole_0(A_167,B_168)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_8])).

tff(c_1474,plain,(
    ! [D_166,B_2,A_1] :
      ( r2_hidden(D_166,B_2)
      | ~ r2_hidden(D_166,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1454])).

tff(c_23483,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_23455,c_1474])).

tff(c_117,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = A_46
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_129,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_58,c_117])).

tff(c_363,plain,(
    ! [D_88,B_89,A_90] :
      ( ~ r2_hidden(D_88,B_89)
      | ~ r2_hidden(D_88,k4_xboole_0(A_90,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_372,plain,(
    ! [D_88] :
      ( ~ r2_hidden(D_88,'#skF_5')
      | ~ r2_hidden(D_88,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_363])).

tff(c_23497,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_23483,c_372])).

tff(c_23504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_23497])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.37  % Computer   : n022.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 11:43:25 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.38  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.21/5.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.21/5.15  
% 12.21/5.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.21/5.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 12.21/5.15  
% 12.21/5.15  %Foreground sorts:
% 12.21/5.15  
% 12.21/5.15  
% 12.21/5.15  %Background operators:
% 12.21/5.15  
% 12.21/5.15  
% 12.21/5.15  %Foreground operators:
% 12.21/5.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.21/5.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.21/5.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.21/5.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.21/5.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.21/5.15  tff('#skF_7', type, '#skF_7': $i).
% 12.21/5.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.21/5.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.21/5.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.21/5.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.21/5.15  tff('#skF_5', type, '#skF_5': $i).
% 12.21/5.15  tff('#skF_6', type, '#skF_6': $i).
% 12.21/5.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.21/5.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.21/5.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.21/5.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.21/5.15  tff('#skF_4', type, '#skF_4': $i).
% 12.21/5.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.21/5.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.21/5.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.21/5.15  
% 12.21/5.17  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 12.21/5.17  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.21/5.17  tff(f_79, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 12.21/5.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.21/5.17  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 12.21/5.17  tff(f_102, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 12.21/5.17  tff(f_91, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 12.21/5.17  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 12.21/5.17  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.21/5.17  tff(f_87, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 12.21/5.17  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.21/5.17  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.21/5.17  tff(c_58, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.21/5.17  tff(c_106, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | ~r1_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.21/5.17  tff(c_112, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_106])).
% 12.21/5.17  tff(c_1081, plain, (![A_137, C_138, B_139]: (~r1_xboole_0(A_137, C_138) | ~r1_xboole_0(A_137, B_139) | r1_xboole_0(A_137, k2_xboole_0(B_139, C_138)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.21/5.17  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.21/5.17  tff(c_5969, plain, (![B_328, C_329, A_330]: (r1_xboole_0(k2_xboole_0(B_328, C_329), A_330) | ~r1_xboole_0(A_330, C_329) | ~r1_xboole_0(A_330, B_328))), inference(resolution, [status(thm)], [c_1081, c_22])).
% 12.21/5.17  tff(c_56, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.21/5.17  tff(c_6003, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5969, c_56])).
% 12.21/5.17  tff(c_6016, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_6003])).
% 12.21/5.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.21/5.17  tff(c_735, plain, (![A_118, B_119]: (r2_hidden('#skF_3'(A_118, B_119), k3_xboole_0(A_118, B_119)) | r1_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.21/5.17  tff(c_744, plain, (![A_1, B_2]: (r2_hidden('#skF_3'(A_1, B_2), k3_xboole_0(B_2, A_1)) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_735])).
% 12.21/5.17  tff(c_62, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.21/5.17  tff(c_194, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.21/5.17  tff(c_44, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.21/5.17  tff(c_2673, plain, (![A_232, B_233]: (k4_xboole_0(k1_tarski(A_232), B_233)=k1_tarski(A_232) | r2_hidden(A_232, B_233))), inference(resolution, [status(thm)], [c_194, c_44])).
% 12.21/5.17  tff(c_28, plain, (![A_16, C_18, B_17]: (r1_xboole_0(A_16, C_18) | ~r1_tarski(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.21/5.17  tff(c_15054, plain, (![A_618, B_619, A_620]: (r1_xboole_0(A_618, B_619) | ~r1_tarski(A_618, k1_tarski(A_620)) | r2_hidden(A_620, B_619))), inference(superposition, [status(thm), theory('equality')], [c_2673, c_28])).
% 12.21/5.17  tff(c_15058, plain, (![B_621]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), B_621) | r2_hidden('#skF_7', B_621))), inference(resolution, [status(thm)], [c_62, c_15054])).
% 12.21/5.17  tff(c_452, plain, (![A_106, B_107]: (k4_xboole_0(A_106, k4_xboole_0(A_106, B_107))=k3_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.21/5.17  tff(c_42, plain, (![A_27, B_28]: (r1_xboole_0(k4_xboole_0(A_27, B_28), B_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.21/5.17  tff(c_146, plain, (![B_48, A_49]: (r1_xboole_0(B_48, k4_xboole_0(A_49, B_48)))), inference(resolution, [status(thm)], [c_42, c_106])).
% 12.21/5.17  tff(c_158, plain, (![B_48, A_49]: (k4_xboole_0(B_48, k4_xboole_0(A_49, B_48))=B_48)), inference(resolution, [status(thm)], [c_146, c_44])).
% 12.21/5.17  tff(c_516, plain, (![B_111]: (k3_xboole_0(B_111, B_111)=B_111)), inference(superposition, [status(thm), theory('equality')], [c_452, c_158])).
% 12.21/5.17  tff(c_26, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, k3_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.21/5.17  tff(c_525, plain, (![B_111, C_15]: (~r1_xboole_0(B_111, B_111) | ~r2_hidden(C_15, B_111))), inference(superposition, [status(thm), theory('equality')], [c_516, c_26])).
% 12.21/5.17  tff(c_15130, plain, (![C_15]: (~r2_hidden(C_15, k3_xboole_0('#skF_4', '#skF_5')) | r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_15058, c_525])).
% 12.21/5.17  tff(c_23359, plain, (![C_780]: (~r2_hidden(C_780, k3_xboole_0('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_15130])).
% 12.21/5.17  tff(c_23407, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_744, c_23359])).
% 12.21/5.17  tff(c_23454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6016, c_23407])).
% 12.21/5.17  tff(c_23455, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_15130])).
% 12.21/5.17  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.21/5.17  tff(c_1454, plain, (![D_166, A_167, B_168]: (r2_hidden(D_166, A_167) | ~r2_hidden(D_166, k3_xboole_0(A_167, B_168)))), inference(superposition, [status(thm), theory('equality')], [c_452, c_8])).
% 12.21/5.17  tff(c_1474, plain, (![D_166, B_2, A_1]: (r2_hidden(D_166, B_2) | ~r2_hidden(D_166, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1454])).
% 12.21/5.17  tff(c_23483, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_23455, c_1474])).
% 12.21/5.17  tff(c_117, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=A_46 | ~r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.21/5.17  tff(c_129, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_58, c_117])).
% 12.21/5.17  tff(c_363, plain, (![D_88, B_89, A_90]: (~r2_hidden(D_88, B_89) | ~r2_hidden(D_88, k4_xboole_0(A_90, B_89)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.21/5.17  tff(c_372, plain, (![D_88]: (~r2_hidden(D_88, '#skF_5') | ~r2_hidden(D_88, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_363])).
% 12.21/5.17  tff(c_23497, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_23483, c_372])).
% 12.21/5.17  tff(c_23504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_23497])).
% 12.21/5.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.21/5.17  
% 12.21/5.17  Inference rules
% 12.21/5.17  ----------------------
% 12.21/5.17  #Ref     : 1
% 12.21/5.17  #Sup     : 5922
% 12.21/5.17  #Fact    : 0
% 12.21/5.17  #Define  : 0
% 12.21/5.17  #Split   : 12
% 12.21/5.17  #Chain   : 0
% 12.21/5.17  #Close   : 0
% 12.21/5.17  
% 12.21/5.17  Ordering : KBO
% 12.21/5.17  
% 12.21/5.17  Simplification rules
% 12.21/5.17  ----------------------
% 12.21/5.17  #Subsume      : 1309
% 12.21/5.17  #Demod        : 2752
% 12.21/5.17  #Tautology    : 1642
% 12.21/5.17  #SimpNegUnit  : 68
% 12.21/5.17  #BackRed      : 19
% 12.21/5.17  
% 12.21/5.17  #Partial instantiations: 0
% 12.21/5.17  #Strategies tried      : 1
% 12.21/5.17  
% 12.21/5.17  Timing (in seconds)
% 12.21/5.17  ----------------------
% 12.21/5.17  Preprocessing        : 0.43
% 12.21/5.17  Parsing              : 0.21
% 12.21/5.17  CNF conversion       : 0.03
% 12.21/5.17  Main loop            : 3.92
% 12.21/5.17  Inferencing          : 0.85
% 12.21/5.17  Reduction            : 1.56
% 12.21/5.17  Demodulation         : 1.21
% 12.21/5.17  BG Simplification    : 0.11
% 12.21/5.17  Subsumption          : 1.13
% 12.21/5.17  Abstraction          : 0.13
% 12.21/5.17  MUC search           : 0.00
% 12.21/5.17  Cooper               : 0.00
% 12.21/5.17  Total                : 4.38
% 12.21/5.17  Index Insertion      : 0.00
% 12.21/5.17  Index Deletion       : 0.00
% 12.21/5.17  Index Matching       : 0.00
% 12.21/5.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
