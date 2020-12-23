%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:34 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 133 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 214 expanded)
%              Number of equality atoms :   37 (  89 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_5

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_100,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_102,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_108,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_70,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_180,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    ! [E_29,A_23,B_24] : r2_hidden(E_29,k1_enumset1(A_23,B_24,E_29)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_207,plain,(
    ! [B_70,A_71] : r2_hidden(B_70,k2_tarski(A_71,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_48])).

tff(c_216,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_207])).

tff(c_38,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_131,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_235,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(B_78,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_131])).

tff(c_78,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_241,plain,(
    ! [B_78,A_77] : k2_xboole_0(B_78,A_77) = k2_xboole_0(A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_78])).

tff(c_82,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_261,plain,(
    r1_tarski(k2_xboole_0('#skF_7',k1_tarski('#skF_6')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_82])).

tff(c_349,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_351,plain,
    ( k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_261,c_349])).

tff(c_362,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_351])).

tff(c_34,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,C_16)
      | ~ r1_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_403,plain,(
    ! [A_96] :
      ( r1_xboole_0(A_96,k1_tarski('#skF_6'))
      | ~ r1_xboole_0(A_96,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_34])).

tff(c_40,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_407,plain,(
    ! [A_96] :
      ( k4_xboole_0(A_96,k1_tarski('#skF_6')) = A_96
      | ~ r1_xboole_0(A_96,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_403,c_40])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_442,plain,(
    ! [A_103,B_104,C_105] :
      ( ~ r1_xboole_0(A_103,B_104)
      | ~ r2_hidden(C_105,B_104)
      | ~ r2_hidden(C_105,A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_623,plain,(
    ! [C_133,B_134,A_135] :
      ( ~ r2_hidden(C_133,B_134)
      | ~ r2_hidden(C_133,A_135)
      | k4_xboole_0(A_135,B_134) != A_135 ) ),
    inference(resolution,[status(thm)],[c_42,c_442])).

tff(c_651,plain,(
    ! [A_136,A_137] :
      ( ~ r2_hidden(A_136,A_137)
      | k4_xboole_0(A_137,k1_tarski(A_136)) != A_137 ) ),
    inference(resolution,[status(thm)],[c_216,c_623])).

tff(c_673,plain,(
    ! [A_140] :
      ( ~ r2_hidden('#skF_6',A_140)
      | ~ r1_xboole_0(A_140,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_651])).

tff(c_704,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_216,c_673])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_832,plain,(
    ! [E_156,C_157,B_158,A_159] :
      ( E_156 = C_157
      | E_156 = B_158
      | E_156 = A_159
      | ~ r2_hidden(E_156,k1_enumset1(A_159,B_158,C_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1024,plain,(
    ! [E_196,B_197,A_198] :
      ( E_196 = B_197
      | E_196 = A_198
      | E_196 = A_198
      | ~ r2_hidden(E_196,k2_tarski(A_198,B_197)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_832])).

tff(c_1054,plain,(
    ! [E_199,A_200] :
      ( E_199 = A_200
      | E_199 = A_200
      | E_199 = A_200
      | ~ r2_hidden(E_199,k1_tarski(A_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1024])).

tff(c_1070,plain,(
    ! [A_201,B_202] :
      ( '#skF_3'(k1_tarski(A_201),B_202) = A_201
      | r1_xboole_0(k1_tarski(A_201),B_202) ) ),
    inference(resolution,[status(thm)],[c_24,c_1054])).

tff(c_1091,plain,(
    '#skF_3'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1070,c_704])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1185,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_22])).

tff(c_1191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_80,c_1185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:12:20 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.52  
% 3.04/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_5
% 3.04/1.52  
% 3.04/1.52  %Foreground sorts:
% 3.04/1.52  
% 3.04/1.52  
% 3.04/1.52  %Background operators:
% 3.04/1.52  
% 3.04/1.52  
% 3.04/1.52  %Foreground operators:
% 3.04/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.04/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.04/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.04/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.04/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.04/1.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.52  
% 3.37/1.54  tff(f_100, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.37/1.54  tff(f_102, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.37/1.54  tff(f_98, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.37/1.54  tff(f_77, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.37/1.54  tff(f_83, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.37/1.54  tff(f_108, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.37/1.54  tff(f_113, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.37/1.54  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.37/1.54  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.37/1.54  tff(f_81, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.37/1.54  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.37/1.54  tff(c_70, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.37/1.54  tff(c_180, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.54  tff(c_48, plain, (![E_29, A_23, B_24]: (r2_hidden(E_29, k1_enumset1(A_23, B_24, E_29)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.54  tff(c_207, plain, (![B_70, A_71]: (r2_hidden(B_70, k2_tarski(A_71, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_180, c_48])).
% 3.37/1.54  tff(c_216, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_207])).
% 3.37/1.54  tff(c_38, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.37/1.54  tff(c_44, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.37/1.54  tff(c_131, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.37/1.54  tff(c_235, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(B_78, A_77))), inference(superposition, [status(thm), theory('equality')], [c_44, c_131])).
% 3.37/1.54  tff(c_78, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.37/1.54  tff(c_241, plain, (![B_78, A_77]: (k2_xboole_0(B_78, A_77)=k2_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_235, c_78])).
% 3.37/1.54  tff(c_82, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.37/1.54  tff(c_261, plain, (r1_tarski(k2_xboole_0('#skF_7', k1_tarski('#skF_6')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_82])).
% 3.37/1.54  tff(c_349, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.37/1.54  tff(c_351, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_261, c_349])).
% 3.37/1.54  tff(c_362, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_351])).
% 3.37/1.54  tff(c_34, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, C_16) | ~r1_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.37/1.54  tff(c_403, plain, (![A_96]: (r1_xboole_0(A_96, k1_tarski('#skF_6')) | ~r1_xboole_0(A_96, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_362, c_34])).
% 3.37/1.54  tff(c_40, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.54  tff(c_407, plain, (![A_96]: (k4_xboole_0(A_96, k1_tarski('#skF_6'))=A_96 | ~r1_xboole_0(A_96, '#skF_7'))), inference(resolution, [status(thm)], [c_403, c_40])).
% 3.37/1.54  tff(c_42, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.54  tff(c_442, plain, (![A_103, B_104, C_105]: (~r1_xboole_0(A_103, B_104) | ~r2_hidden(C_105, B_104) | ~r2_hidden(C_105, A_103))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.54  tff(c_623, plain, (![C_133, B_134, A_135]: (~r2_hidden(C_133, B_134) | ~r2_hidden(C_133, A_135) | k4_xboole_0(A_135, B_134)!=A_135)), inference(resolution, [status(thm)], [c_42, c_442])).
% 3.37/1.54  tff(c_651, plain, (![A_136, A_137]: (~r2_hidden(A_136, A_137) | k4_xboole_0(A_137, k1_tarski(A_136))!=A_137)), inference(resolution, [status(thm)], [c_216, c_623])).
% 3.37/1.54  tff(c_673, plain, (![A_140]: (~r2_hidden('#skF_6', A_140) | ~r1_xboole_0(A_140, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_407, c_651])).
% 3.37/1.54  tff(c_704, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_216, c_673])).
% 3.37/1.54  tff(c_80, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.37/1.54  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.54  tff(c_72, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.54  tff(c_832, plain, (![E_156, C_157, B_158, A_159]: (E_156=C_157 | E_156=B_158 | E_156=A_159 | ~r2_hidden(E_156, k1_enumset1(A_159, B_158, C_157)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.54  tff(c_1024, plain, (![E_196, B_197, A_198]: (E_196=B_197 | E_196=A_198 | E_196=A_198 | ~r2_hidden(E_196, k2_tarski(A_198, B_197)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_832])).
% 3.37/1.54  tff(c_1054, plain, (![E_199, A_200]: (E_199=A_200 | E_199=A_200 | E_199=A_200 | ~r2_hidden(E_199, k1_tarski(A_200)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1024])).
% 3.37/1.54  tff(c_1070, plain, (![A_201, B_202]: ('#skF_3'(k1_tarski(A_201), B_202)=A_201 | r1_xboole_0(k1_tarski(A_201), B_202))), inference(resolution, [status(thm)], [c_24, c_1054])).
% 3.37/1.54  tff(c_1091, plain, ('#skF_3'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1070, c_704])).
% 3.37/1.54  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.54  tff(c_1185, plain, (r2_hidden('#skF_6', '#skF_7') | r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1091, c_22])).
% 3.37/1.54  tff(c_1191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_80, c_1185])).
% 3.37/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.54  
% 3.37/1.54  Inference rules
% 3.37/1.54  ----------------------
% 3.37/1.54  #Ref     : 0
% 3.37/1.54  #Sup     : 263
% 3.37/1.54  #Fact    : 0
% 3.37/1.54  #Define  : 0
% 3.37/1.54  #Split   : 1
% 3.37/1.54  #Chain   : 0
% 3.37/1.54  #Close   : 0
% 3.37/1.54  
% 3.37/1.54  Ordering : KBO
% 3.37/1.54  
% 3.37/1.54  Simplification rules
% 3.37/1.54  ----------------------
% 3.37/1.54  #Subsume      : 72
% 3.37/1.54  #Demod        : 37
% 3.37/1.54  #Tautology    : 79
% 3.37/1.54  #SimpNegUnit  : 2
% 3.37/1.54  #BackRed      : 2
% 3.37/1.54  
% 3.37/1.54  #Partial instantiations: 0
% 3.37/1.54  #Strategies tried      : 1
% 3.37/1.54  
% 3.37/1.54  Timing (in seconds)
% 3.37/1.54  ----------------------
% 3.37/1.54  Preprocessing        : 0.34
% 3.37/1.54  Parsing              : 0.17
% 3.37/1.54  CNF conversion       : 0.03
% 3.37/1.54  Main loop            : 0.42
% 3.37/1.54  Inferencing          : 0.14
% 3.37/1.54  Reduction            : 0.14
% 3.37/1.54  Demodulation         : 0.10
% 3.37/1.54  BG Simplification    : 0.02
% 3.37/1.54  Subsumption          : 0.09
% 3.37/1.54  Abstraction          : 0.03
% 3.37/1.54  MUC search           : 0.00
% 3.37/1.54  Cooper               : 0.00
% 3.37/1.54  Total                : 0.79
% 3.37/1.54  Index Insertion      : 0.00
% 3.37/1.54  Index Deletion       : 0.00
% 3.37/1.54  Index Matching       : 0.00
% 3.37/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
