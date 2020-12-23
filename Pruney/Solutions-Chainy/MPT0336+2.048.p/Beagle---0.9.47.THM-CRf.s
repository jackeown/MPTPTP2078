%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:06 EST 2020

% Result     : Theorem 4.98s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 107 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 161 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_20,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_17] : r1_xboole_0(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_161,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [A_17] : k3_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_161])).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_185,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_161])).

tff(c_630,plain,(
    ! [A_98,B_99,C_100] : k3_xboole_0(k3_xboole_0(A_98,B_99),C_100) = k3_xboole_0(A_98,k3_xboole_0(B_99,C_100)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_697,plain,(
    ! [C_100] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_100)) = k3_xboole_0(k1_xboole_0,C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_630])).

tff(c_730,plain,(
    ! [C_100] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_100)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_697])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(k1_tarski(A_27),B_28)
      | r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_356,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(k1_tarski(A_67),B_68) = k1_xboole_0
      | r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_34,c_161])).

tff(c_475,plain,(
    ! [A_79,A_80] :
      ( k3_xboole_0(A_79,k1_tarski(A_80)) = k1_xboole_0
      | r2_hidden(A_80,A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_356])).

tff(c_44,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_45,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_143,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_147,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_143])).

tff(c_485,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_147])).

tff(c_3278,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_414,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,B_72)
      | ~ r2_hidden(C_73,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3237,plain,(
    ! [C_140,B_141,A_142] :
      ( ~ r2_hidden(C_140,B_141)
      | ~ r2_hidden(C_140,A_142)
      | k3_xboole_0(A_142,B_141) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_414])).

tff(c_3255,plain,(
    ! [A_142] :
      ( ~ r2_hidden('#skF_5',A_142)
      | k3_xboole_0(A_142,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_3237])).

tff(c_3281,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3278,c_3255])).

tff(c_3289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_2,c_3281])).

tff(c_3290,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_148,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_154,plain,(
    ! [B_46,A_45] :
      ( r1_xboole_0(B_46,A_45)
      | k3_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_148,c_8])).

tff(c_62,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_1056,plain,(
    ! [A_107,C_108,B_109] :
      ( ~ r1_xboole_0(A_107,C_108)
      | ~ r1_xboole_0(A_107,B_109)
      | r1_xboole_0(A_107,k2_xboole_0(B_109,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4948,plain,(
    ! [B_162,C_163,A_164] :
      ( r1_xboole_0(k2_xboole_0(B_162,C_163),A_164)
      | ~ r1_xboole_0(A_164,C_163)
      | ~ r1_xboole_0(A_164,B_162) ) ),
    inference(resolution,[status(thm)],[c_1056,c_8])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4970,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4948,c_38])).

tff(c_4982,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4970])).

tff(c_4985,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_4982])).

tff(c_4992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3290,c_2,c_4985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.98/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/1.97  
% 5.12/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/1.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.12/1.97  
% 5.12/1.97  %Foreground sorts:
% 5.12/1.97  
% 5.12/1.97  
% 5.12/1.97  %Background operators:
% 5.12/1.97  
% 5.12/1.97  
% 5.12/1.97  %Foreground operators:
% 5.12/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.12/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.12/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.12/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.12/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.12/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.12/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.12/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.12/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.12/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.12/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.12/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/1.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.12/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.12/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.12/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.12/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.12/1.97  
% 5.12/1.99  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.12/1.99  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.12/1.99  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.12/1.99  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.12/1.99  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.12/1.99  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.12/1.99  tff(f_88, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.12/1.99  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.12/1.99  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.12/1.99  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.12/1.99  tff(c_20, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.12/1.99  tff(c_56, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.12/1.99  tff(c_61, plain, (![A_17]: (r1_xboole_0(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_20, c_56])).
% 5.12/1.99  tff(c_161, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.12/1.99  tff(c_183, plain, (![A_17]: (k3_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_161])).
% 5.12/1.99  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.12/1.99  tff(c_185, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_161])).
% 5.12/1.99  tff(c_630, plain, (![A_98, B_99, C_100]: (k3_xboole_0(k3_xboole_0(A_98, B_99), C_100)=k3_xboole_0(A_98, k3_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.12/1.99  tff(c_697, plain, (![C_100]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_100))=k3_xboole_0(k1_xboole_0, C_100))), inference(superposition, [status(thm), theory('equality')], [c_185, c_630])).
% 5.12/1.99  tff(c_730, plain, (![C_100]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_100))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_697])).
% 5.12/1.99  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/1.99  tff(c_34, plain, (![A_27, B_28]: (r1_xboole_0(k1_tarski(A_27), B_28) | r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.12/1.99  tff(c_356, plain, (![A_67, B_68]: (k3_xboole_0(k1_tarski(A_67), B_68)=k1_xboole_0 | r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_34, c_161])).
% 5.12/1.99  tff(c_475, plain, (![A_79, A_80]: (k3_xboole_0(A_79, k1_tarski(A_80))=k1_xboole_0 | r2_hidden(A_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_2, c_356])).
% 5.12/1.99  tff(c_44, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.12/1.99  tff(c_45, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 5.12/1.99  tff(c_143, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.12/1.99  tff(c_147, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_45, c_143])).
% 5.12/1.99  tff(c_485, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_475, c_147])).
% 5.12/1.99  tff(c_3278, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_485])).
% 5.12/1.99  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.12/1.99  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.12/1.99  tff(c_414, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, B_72) | ~r2_hidden(C_73, A_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.12/1.99  tff(c_3237, plain, (![C_140, B_141, A_142]: (~r2_hidden(C_140, B_141) | ~r2_hidden(C_140, A_142) | k3_xboole_0(A_142, B_141)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_414])).
% 5.12/1.99  tff(c_3255, plain, (![A_142]: (~r2_hidden('#skF_5', A_142) | k3_xboole_0(A_142, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_3237])).
% 5.12/1.99  tff(c_3281, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3278, c_3255])).
% 5.12/1.99  tff(c_3289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_730, c_2, c_3281])).
% 5.12/1.99  tff(c_3290, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_485])).
% 5.12/1.99  tff(c_148, plain, (![A_45, B_46]: (r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.12/1.99  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.12/1.99  tff(c_154, plain, (![B_46, A_45]: (r1_xboole_0(B_46, A_45) | k3_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_148, c_8])).
% 5.12/1.99  tff(c_62, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_56])).
% 5.12/1.99  tff(c_1056, plain, (![A_107, C_108, B_109]: (~r1_xboole_0(A_107, C_108) | ~r1_xboole_0(A_107, B_109) | r1_xboole_0(A_107, k2_xboole_0(B_109, C_108)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.12/1.99  tff(c_4948, plain, (![B_162, C_163, A_164]: (r1_xboole_0(k2_xboole_0(B_162, C_163), A_164) | ~r1_xboole_0(A_164, C_163) | ~r1_xboole_0(A_164, B_162))), inference(resolution, [status(thm)], [c_1056, c_8])).
% 5.12/1.99  tff(c_38, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.12/1.99  tff(c_4970, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4948, c_38])).
% 5.12/1.99  tff(c_4982, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4970])).
% 5.12/1.99  tff(c_4985, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_4982])).
% 5.12/1.99  tff(c_4992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3290, c_2, c_4985])).
% 5.12/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/1.99  
% 5.12/1.99  Inference rules
% 5.12/1.99  ----------------------
% 5.12/1.99  #Ref     : 0
% 5.12/1.99  #Sup     : 1261
% 5.12/1.99  #Fact    : 0
% 5.12/1.99  #Define  : 0
% 5.12/1.99  #Split   : 2
% 5.12/1.99  #Chain   : 0
% 5.12/1.99  #Close   : 0
% 5.12/1.99  
% 5.12/1.99  Ordering : KBO
% 5.12/1.99  
% 5.12/1.99  Simplification rules
% 5.12/1.99  ----------------------
% 5.12/1.99  #Subsume      : 27
% 5.12/1.99  #Demod        : 1195
% 5.12/1.99  #Tautology    : 864
% 5.12/1.99  #SimpNegUnit  : 1
% 5.12/1.99  #BackRed      : 4
% 5.12/1.99  
% 5.12/1.99  #Partial instantiations: 0
% 5.12/1.99  #Strategies tried      : 1
% 5.12/1.99  
% 5.12/1.99  Timing (in seconds)
% 5.12/1.99  ----------------------
% 5.12/1.99  Preprocessing        : 0.30
% 5.12/1.99  Parsing              : 0.16
% 5.12/1.99  CNF conversion       : 0.02
% 5.12/1.99  Main loop            : 0.89
% 5.12/1.99  Inferencing          : 0.25
% 5.12/1.99  Reduction            : 0.44
% 5.12/1.99  Demodulation         : 0.38
% 5.12/1.99  BG Simplification    : 0.03
% 5.12/1.99  Subsumption          : 0.12
% 5.12/1.99  Abstraction          : 0.04
% 5.12/1.99  MUC search           : 0.00
% 5.12/1.99  Cooper               : 0.00
% 5.12/1.99  Total                : 1.22
% 5.12/1.99  Index Insertion      : 0.00
% 5.12/1.99  Index Deletion       : 0.00
% 5.12/1.99  Index Matching       : 0.00
% 5.12/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
