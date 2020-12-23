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
% DateTime   : Thu Dec  3 09:55:02 EST 2020

% Result     : Theorem 6.49s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 114 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 178 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_55,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_46,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_171,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_195,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_171])).

tff(c_274,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_283,plain,(
    ! [C_63] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_63,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_274])).

tff(c_298,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_283])).

tff(c_26,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_196,plain,(
    ! [A_59] : k3_xboole_0(A_59,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_171])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_201,plain,(
    ! [A_59] : k3_xboole_0(k1_xboole_0,A_59) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_4])).

tff(c_899,plain,(
    ! [A_109,B_110,C_111] : k3_xboole_0(k3_xboole_0(A_109,B_110),C_111) = k3_xboole_0(A_109,k3_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_976,plain,(
    ! [C_111] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',C_111)) = k3_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_899])).

tff(c_1009,plain,(
    ! [C_111] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',C_111)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_976])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_51,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_148,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_152,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_148])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),B_39)
      | r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_462,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(k1_tarski(A_82),B_83) = k1_xboole_0
      | r2_hidden(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_42,c_171])).

tff(c_629,plain,(
    ! [B_93,A_94] :
      ( k3_xboole_0(B_93,k1_tarski(A_94)) = k1_xboole_0
      | r2_hidden(A_94,B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_4])).

tff(c_671,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_629])).

tff(c_2548,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_671])).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_800,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r1_xboole_0(A_101,B_102)
      | ~ r2_hidden(C_103,B_102)
      | ~ r2_hidden(C_103,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3987,plain,(
    ! [C_177,B_178,A_179] :
      ( ~ r2_hidden(C_177,B_178)
      | ~ r2_hidden(C_177,A_179)
      | k3_xboole_0(A_179,B_178) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_800])).

tff(c_4012,plain,(
    ! [A_180] :
      ( ~ r2_hidden('#skF_6',A_180)
      | k3_xboole_0(A_180,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_3987])).

tff(c_4019,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2548,c_4012])).

tff(c_4035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_4,c_4019])).

tff(c_4036,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_2'(A_14,B_15),k3_xboole_0(A_14,B_15))
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4053,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4036,c_18])).

tff(c_4086,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_4053])).

tff(c_62,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | ~ r1_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_62])).

tff(c_1927,plain,(
    ! [A_132,C_133,B_134] :
      ( ~ r1_xboole_0(A_132,C_133)
      | ~ r1_xboole_0(A_132,B_134)
      | r1_xboole_0(A_132,k2_xboole_0(B_134,C_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8766,plain,(
    ! [B_257,C_258,A_259] :
      ( r1_xboole_0(k2_xboole_0(B_257,C_258),A_259)
      | ~ r1_xboole_0(A_259,C_258)
      | ~ r1_xboole_0(A_259,B_257) ) ),
    inference(resolution,[status(thm)],[c_1927,c_10])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8784,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8766,c_44])).

tff(c_8799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4086,c_68,c_8784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.49/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.34  
% 6.64/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.64/2.34  
% 6.64/2.34  %Foreground sorts:
% 6.64/2.34  
% 6.64/2.34  
% 6.64/2.34  %Background operators:
% 6.64/2.34  
% 6.64/2.34  
% 6.64/2.34  %Foreground operators:
% 6.64/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.64/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.64/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.64/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.64/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.64/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.64/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.64/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.64/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.64/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.64/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.64/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.64/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.64/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.64/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.64/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.64/2.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.64/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.64/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.64/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.64/2.34  
% 6.64/2.35  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.64/2.35  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.64/2.35  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.64/2.35  tff(f_77, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.64/2.35  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.64/2.35  tff(f_71, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.64/2.35  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.64/2.35  tff(f_106, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.64/2.35  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.64/2.35  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.64/2.35  tff(f_93, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.64/2.35  tff(c_46, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.64/2.35  tff(c_171, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.64/2.35  tff(c_195, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_171])).
% 6.64/2.35  tff(c_274, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.64/2.35  tff(c_283, plain, (![C_63]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_195, c_274])).
% 6.64/2.35  tff(c_298, plain, (![C_63]: (~r2_hidden(C_63, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_283])).
% 6.64/2.35  tff(c_26, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.64/2.35  tff(c_196, plain, (![A_59]: (k3_xboole_0(A_59, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_171])).
% 6.64/2.35  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.64/2.35  tff(c_201, plain, (![A_59]: (k3_xboole_0(k1_xboole_0, A_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_196, c_4])).
% 6.64/2.35  tff(c_899, plain, (![A_109, B_110, C_111]: (k3_xboole_0(k3_xboole_0(A_109, B_110), C_111)=k3_xboole_0(A_109, k3_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.64/2.35  tff(c_976, plain, (![C_111]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', C_111))=k3_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_195, c_899])).
% 6.64/2.35  tff(c_1009, plain, (![C_111]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', C_111))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_976])).
% 6.64/2.35  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.64/2.35  tff(c_51, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_50])).
% 6.64/2.35  tff(c_148, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.64/2.35  tff(c_152, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_148])).
% 6.64/2.35  tff(c_42, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), B_39) | r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.64/2.35  tff(c_462, plain, (![A_82, B_83]: (k3_xboole_0(k1_tarski(A_82), B_83)=k1_xboole_0 | r2_hidden(A_82, B_83))), inference(resolution, [status(thm)], [c_42, c_171])).
% 6.64/2.35  tff(c_629, plain, (![B_93, A_94]: (k3_xboole_0(B_93, k1_tarski(A_94))=k1_xboole_0 | r2_hidden(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_462, c_4])).
% 6.64/2.35  tff(c_671, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_629])).
% 6.64/2.35  tff(c_2548, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_671])).
% 6.64/2.35  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.64/2.35  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.64/2.35  tff(c_800, plain, (![A_101, B_102, C_103]: (~r1_xboole_0(A_101, B_102) | ~r2_hidden(C_103, B_102) | ~r2_hidden(C_103, A_101))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.64/2.35  tff(c_3987, plain, (![C_177, B_178, A_179]: (~r2_hidden(C_177, B_178) | ~r2_hidden(C_177, A_179) | k3_xboole_0(A_179, B_178)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_800])).
% 6.64/2.35  tff(c_4012, plain, (![A_180]: (~r2_hidden('#skF_6', A_180) | k3_xboole_0(A_180, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_3987])).
% 6.64/2.35  tff(c_4019, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2548, c_4012])).
% 6.64/2.35  tff(c_4035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1009, c_4, c_4019])).
% 6.64/2.35  tff(c_4036, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_671])).
% 6.64/2.35  tff(c_18, plain, (![A_14, B_15]: (r2_hidden('#skF_2'(A_14, B_15), k3_xboole_0(A_14, B_15)) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.64/2.35  tff(c_4053, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4036, c_18])).
% 6.64/2.35  tff(c_4086, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_298, c_4053])).
% 6.64/2.35  tff(c_62, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | ~r1_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.64/2.35  tff(c_68, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_62])).
% 6.64/2.35  tff(c_1927, plain, (![A_132, C_133, B_134]: (~r1_xboole_0(A_132, C_133) | ~r1_xboole_0(A_132, B_134) | r1_xboole_0(A_132, k2_xboole_0(B_134, C_133)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.64/2.35  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.64/2.35  tff(c_8766, plain, (![B_257, C_258, A_259]: (r1_xboole_0(k2_xboole_0(B_257, C_258), A_259) | ~r1_xboole_0(A_259, C_258) | ~r1_xboole_0(A_259, B_257))), inference(resolution, [status(thm)], [c_1927, c_10])).
% 6.64/2.35  tff(c_44, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.64/2.35  tff(c_8784, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8766, c_44])).
% 6.64/2.35  tff(c_8799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4086, c_68, c_8784])).
% 6.64/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.36  
% 6.64/2.36  Inference rules
% 6.64/2.36  ----------------------
% 6.64/2.36  #Ref     : 0
% 6.64/2.36  #Sup     : 2174
% 6.64/2.36  #Fact    : 0
% 6.64/2.36  #Define  : 0
% 6.64/2.36  #Split   : 4
% 6.64/2.36  #Chain   : 0
% 6.64/2.36  #Close   : 0
% 6.64/2.36  
% 6.64/2.36  Ordering : KBO
% 6.64/2.36  
% 6.64/2.36  Simplification rules
% 6.64/2.36  ----------------------
% 6.64/2.36  #Subsume      : 152
% 6.64/2.36  #Demod        : 1933
% 6.64/2.36  #Tautology    : 1413
% 6.64/2.36  #SimpNegUnit  : 61
% 6.64/2.36  #BackRed      : 4
% 6.64/2.36  
% 6.64/2.36  #Partial instantiations: 0
% 6.64/2.36  #Strategies tried      : 1
% 6.64/2.36  
% 6.64/2.36  Timing (in seconds)
% 6.64/2.36  ----------------------
% 6.64/2.36  Preprocessing        : 0.31
% 6.64/2.36  Parsing              : 0.17
% 6.64/2.36  CNF conversion       : 0.02
% 6.64/2.36  Main loop            : 1.28
% 6.64/2.36  Inferencing          : 0.34
% 6.64/2.36  Reduction            : 0.63
% 6.64/2.36  Demodulation         : 0.53
% 6.64/2.36  BG Simplification    : 0.04
% 6.64/2.36  Subsumption          : 0.20
% 6.64/2.36  Abstraction          : 0.05
% 6.64/2.36  MUC search           : 0.00
% 6.64/2.36  Cooper               : 0.00
% 6.64/2.36  Total                : 1.62
% 6.64/2.36  Index Insertion      : 0.00
% 6.64/2.36  Index Deletion       : 0.00
% 6.64/2.36  Index Matching       : 0.00
% 6.64/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
