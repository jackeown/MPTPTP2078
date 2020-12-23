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
% DateTime   : Thu Dec  3 09:55:06 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 131 expanded)
%              Number of equality atoms :    9 (  16 expanded)
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

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),k3_xboole_0(A_11,B_12))
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(k1_tarski(A_34),B_35)
      | r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_307,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | r1_xboole_0(A_73,k3_xboole_0(B_74,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_318,plain,(
    ! [A_73,A_1,B_2] :
      ( ~ r1_xboole_0(A_73,A_1)
      | r1_xboole_0(A_73,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_307])).

tff(c_58,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_109,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_113,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_109])).

tff(c_219,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_324,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(B_77,A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_219])).

tff(c_327,plain,(
    ! [C_78] :
      ( ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5'))
      | ~ r2_hidden(C_78,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_324])).

tff(c_1747,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_1779,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_318,c_1747])).

tff(c_1811,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_1779])).

tff(c_54,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_151,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = A_49
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_167,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_151])).

tff(c_280,plain,(
    ! [D_69,B_70,A_71] :
      ( ~ r2_hidden(D_69,B_70)
      | ~ r2_hidden(D_69,k4_xboole_0(A_71,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_292,plain,(
    ! [D_69] :
      ( ~ r2_hidden(D_69,'#skF_5')
      | ~ r2_hidden(D_69,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_280])).

tff(c_1814,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_1811,c_292])).

tff(c_1818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1814])).

tff(c_1842,plain,(
    ! [C_173] : ~ r2_hidden(C_173,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_1877,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1842])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1884,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1877,c_22])).

tff(c_68,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_652,plain,(
    ! [A_113,C_114,B_115] :
      ( ~ r1_xboole_0(A_113,C_114)
      | ~ r1_xboole_0(A_113,B_115)
      | r1_xboole_0(A_113,k2_xboole_0(B_115,C_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3398,plain,(
    ! [B_210,C_211,A_212] :
      ( r1_xboole_0(k2_xboole_0(B_210,C_211),A_212)
      | ~ r1_xboole_0(A_212,C_211)
      | ~ r1_xboole_0(A_212,B_210) ) ),
    inference(resolution,[status(thm)],[c_652,c_22])).

tff(c_52,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3423,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3398,c_52])).

tff(c_3434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_71,c_3423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.91  
% 4.55/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.91  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.55/1.91  
% 4.55/1.91  %Foreground sorts:
% 4.55/1.91  
% 4.55/1.91  
% 4.55/1.91  %Background operators:
% 4.55/1.91  
% 4.55/1.91  
% 4.55/1.91  %Foreground operators:
% 4.55/1.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.55/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.55/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.55/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.55/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.55/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.55/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.55/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.55/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.55/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.55/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.55/1.91  
% 4.55/1.92  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.55/1.92  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.55/1.92  tff(f_98, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.55/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.55/1.92  tff(f_83, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 4.55/1.92  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.55/1.92  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.55/1.92  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.55/1.92  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.55/1.92  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.55/1.92  tff(c_24, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), k3_xboole_0(A_11, B_12)) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.92  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.92  tff(c_50, plain, (![A_34, B_35]: (r1_xboole_0(k1_tarski(A_34), B_35) | r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.55/1.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.92  tff(c_307, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | r1_xboole_0(A_73, k3_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.55/1.92  tff(c_318, plain, (![A_73, A_1, B_2]: (~r1_xboole_0(A_73, A_1) | r1_xboole_0(A_73, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_307])).
% 4.55/1.92  tff(c_58, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.92  tff(c_109, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.55/1.92  tff(c_113, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_109])).
% 4.55/1.92  tff(c_219, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.92  tff(c_324, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(B_77, A_76)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_219])).
% 4.55/1.92  tff(c_327, plain, (![C_78]: (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5')) | ~r2_hidden(C_78, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_113, c_324])).
% 4.55/1.92  tff(c_1747, plain, (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_327])).
% 4.55/1.92  tff(c_1779, plain, (~r1_xboole_0(k1_tarski('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_318, c_1747])).
% 4.55/1.92  tff(c_1811, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_1779])).
% 4.55/1.92  tff(c_54, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.92  tff(c_151, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=A_49 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.55/1.92  tff(c_167, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_54, c_151])).
% 4.55/1.92  tff(c_280, plain, (![D_69, B_70, A_71]: (~r2_hidden(D_69, B_70) | ~r2_hidden(D_69, k4_xboole_0(A_71, B_70)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.92  tff(c_292, plain, (![D_69]: (~r2_hidden(D_69, '#skF_5') | ~r2_hidden(D_69, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_280])).
% 4.55/1.92  tff(c_1814, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_1811, c_292])).
% 4.55/1.92  tff(c_1818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1814])).
% 4.55/1.92  tff(c_1842, plain, (![C_173]: (~r2_hidden(C_173, k3_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_327])).
% 4.55/1.92  tff(c_1877, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_1842])).
% 4.55/1.92  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.55/1.92  tff(c_1884, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1877, c_22])).
% 4.55/1.92  tff(c_68, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.55/1.92  tff(c_71, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_68])).
% 4.55/1.92  tff(c_652, plain, (![A_113, C_114, B_115]: (~r1_xboole_0(A_113, C_114) | ~r1_xboole_0(A_113, B_115) | r1_xboole_0(A_113, k2_xboole_0(B_115, C_114)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.55/1.92  tff(c_3398, plain, (![B_210, C_211, A_212]: (r1_xboole_0(k2_xboole_0(B_210, C_211), A_212) | ~r1_xboole_0(A_212, C_211) | ~r1_xboole_0(A_212, B_210))), inference(resolution, [status(thm)], [c_652, c_22])).
% 4.55/1.92  tff(c_52, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.92  tff(c_3423, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3398, c_52])).
% 4.55/1.92  tff(c_3434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1884, c_71, c_3423])).
% 4.55/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.92  
% 4.55/1.92  Inference rules
% 4.55/1.92  ----------------------
% 4.55/1.92  #Ref     : 0
% 4.55/1.92  #Sup     : 829
% 4.55/1.92  #Fact    : 0
% 4.55/1.92  #Define  : 0
% 4.55/1.92  #Split   : 3
% 4.55/1.92  #Chain   : 0
% 4.55/1.92  #Close   : 0
% 4.55/1.92  
% 4.55/1.92  Ordering : KBO
% 4.55/1.92  
% 4.55/1.92  Simplification rules
% 4.55/1.92  ----------------------
% 4.55/1.92  #Subsume      : 202
% 4.55/1.92  #Demod        : 230
% 4.55/1.92  #Tautology    : 297
% 4.55/1.92  #SimpNegUnit  : 23
% 4.55/1.92  #BackRed      : 15
% 4.55/1.92  
% 4.55/1.92  #Partial instantiations: 0
% 4.55/1.92  #Strategies tried      : 1
% 4.55/1.92  
% 4.55/1.92  Timing (in seconds)
% 4.55/1.92  ----------------------
% 4.94/1.93  Preprocessing        : 0.31
% 4.94/1.93  Parsing              : 0.15
% 4.94/1.93  CNF conversion       : 0.02
% 4.94/1.93  Main loop            : 0.81
% 4.94/1.93  Inferencing          : 0.26
% 4.94/1.93  Reduction            : 0.26
% 4.94/1.93  Demodulation         : 0.19
% 4.94/1.93  BG Simplification    : 0.03
% 4.94/1.93  Subsumption          : 0.18
% 4.94/1.93  Abstraction          : 0.04
% 4.94/1.93  MUC search           : 0.00
% 4.94/1.93  Cooper               : 0.00
% 4.94/1.93  Total                : 1.15
% 4.94/1.93  Index Insertion      : 0.00
% 4.94/1.93  Index Deletion       : 0.00
% 4.94/1.93  Index Matching       : 0.00
% 4.94/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
