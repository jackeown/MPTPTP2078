%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:12 EST 2020

% Result     : Theorem 6.65s
% Output     : CNFRefutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 109 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 166 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_44,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_713,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,B_90)
      | ~ r2_hidden(C_91,B_90)
      | ~ r2_hidden(C_91,A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_741,plain,(
    ! [C_92] :
      ( ~ r2_hidden(C_92,'#skF_4')
      | ~ r2_hidden(C_92,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_713])).

tff(c_761,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_741])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_971,plain,(
    ! [A_111,C_112,B_113] :
      ( ~ r1_xboole_0(A_111,C_112)
      | ~ r1_xboole_0(A_111,B_113)
      | r1_xboole_0(A_111,k2_xboole_0(B_113,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4548,plain,(
    ! [B_205,C_206,A_207] :
      ( r1_xboole_0(k2_xboole_0(B_205,C_206),A_207)
      | ~ r1_xboole_0(A_207,C_206)
      | ~ r1_xboole_0(A_207,B_205) ) ),
    inference(resolution,[status(thm)],[c_971,c_4])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4566,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4548,c_40])).

tff(c_4574,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_4566])).

tff(c_4586,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_4574])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,k1_tarski(B_31)) = A_30
      | r2_hidden(B_31,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_270,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_xboole_0(A_67,k4_xboole_0(C_68,B_69))
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4287,plain,(
    ! [A_197,A_198,B_199] :
      ( r1_xboole_0(A_197,A_198)
      | ~ r1_tarski(A_197,k1_tarski(B_199))
      | r2_hidden(B_199,A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_270])).

tff(c_4309,plain,(
    ! [A_198] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_198)
      | r2_hidden('#skF_6',A_198) ) ),
    inference(resolution,[status(thm)],[c_47,c_4287])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1278,plain,(
    ! [A_132,C_133,B_134] :
      ( k4_xboole_0(A_132,k4_xboole_0(C_133,B_134)) = A_132
      | ~ r1_tarski(A_132,B_134) ) ),
    inference(resolution,[status(thm)],[c_270,c_26])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1429,plain,(
    ! [C_137,B_138] :
      ( k3_xboole_0(C_137,B_138) = C_137
      | ~ r1_tarski(C_137,B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_18])).

tff(c_2259,plain,(
    ! [A_158,B_159] : k3_xboole_0(k4_xboole_0(A_158,B_159),A_158) = k4_xboole_0(A_158,B_159) ),
    inference(resolution,[status(thm)],[c_16,c_1429])).

tff(c_2321,plain,(
    ! [A_158,B_159] : k3_xboole_0(A_158,k4_xboole_0(A_158,B_159)) = k4_xboole_0(A_158,B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_2259,c_2])).

tff(c_179,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_182,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,k4_xboole_0(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_18])).

tff(c_3854,plain,(
    ! [A_190,B_191] : k4_xboole_0(A_190,k3_xboole_0(A_190,B_191)) = k4_xboole_0(A_190,B_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2321,c_182])).

tff(c_3965,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3854])).

tff(c_264,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_66)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_769,plain,(
    ! [A_93,B_94,A_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | r1_xboole_0(A_95,k3_xboole_0(A_93,B_94)) ) ),
    inference(resolution,[status(thm)],[c_264,c_14])).

tff(c_6609,plain,(
    ! [A_263,A_264,B_265] :
      ( k4_xboole_0(A_263,k3_xboole_0(A_264,B_265)) = A_263
      | ~ r1_xboole_0(A_264,B_265) ) ),
    inference(resolution,[status(thm)],[c_769,c_26])).

tff(c_7950,plain,(
    ! [B_295,A_296] :
      ( k4_xboole_0(B_295,A_296) = B_295
      | ~ r1_xboole_0(A_296,B_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3965,c_6609])).

tff(c_8435,plain,(
    ! [A_303] :
      ( k4_xboole_0(A_303,k3_xboole_0('#skF_4','#skF_3')) = A_303
      | r2_hidden('#skF_6',A_303) ) ),
    inference(resolution,[status(thm)],[c_4309,c_7950])).

tff(c_3581,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2321,c_182])).

tff(c_8485,plain,
    ( k4_xboole_0('#skF_4','#skF_3') = '#skF_4'
    | r2_hidden('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8435,c_3581])).

tff(c_8568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_761,c_4586,c_8485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.65/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.65/2.48  
% 6.65/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.65/2.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.65/2.48  
% 6.65/2.48  %Foreground sorts:
% 6.65/2.48  
% 6.65/2.48  
% 6.65/2.48  %Background operators:
% 6.65/2.48  
% 6.65/2.48  
% 6.65/2.48  %Foreground operators:
% 6.65/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.65/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.65/2.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.65/2.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.65/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.65/2.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.65/2.48  tff('#skF_5', type, '#skF_5': $i).
% 6.65/2.48  tff('#skF_6', type, '#skF_6': $i).
% 6.65/2.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.65/2.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.65/2.48  tff('#skF_3', type, '#skF_3': $i).
% 6.65/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.65/2.48  tff('#skF_4', type, '#skF_4': $i).
% 6.65/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.65/2.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.65/2.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.65/2.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.65/2.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.65/2.48  
% 6.74/2.50  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.74/2.50  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.74/2.50  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.74/2.50  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.74/2.50  tff(f_83, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.74/2.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.74/2.50  tff(f_100, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.74/2.50  tff(f_91, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 6.74/2.50  tff(f_65, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.74/2.50  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.74/2.50  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.74/2.50  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.74/2.50  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.74/2.50  tff(c_713, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, B_90) | ~r2_hidden(C_91, B_90) | ~r2_hidden(C_91, A_89))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.74/2.50  tff(c_741, plain, (![C_92]: (~r2_hidden(C_92, '#skF_4') | ~r2_hidden(C_92, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_713])).
% 6.74/2.50  tff(c_761, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_741])).
% 6.74/2.50  tff(c_28, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.74/2.50  tff(c_58, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.74/2.50  tff(c_61, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_58])).
% 6.74/2.50  tff(c_971, plain, (![A_111, C_112, B_113]: (~r1_xboole_0(A_111, C_112) | ~r1_xboole_0(A_111, B_113) | r1_xboole_0(A_111, k2_xboole_0(B_113, C_112)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.74/2.50  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.74/2.50  tff(c_4548, plain, (![B_205, C_206, A_207]: (r1_xboole_0(k2_xboole_0(B_205, C_206), A_207) | ~r1_xboole_0(A_207, C_206) | ~r1_xboole_0(A_207, B_205))), inference(resolution, [status(thm)], [c_971, c_4])).
% 6.74/2.50  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.74/2.50  tff(c_4566, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4548, c_40])).
% 6.74/2.50  tff(c_4574, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_4566])).
% 6.74/2.50  tff(c_4586, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_28, c_4574])).
% 6.74/2.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.74/2.50  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.74/2.50  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 6.74/2.50  tff(c_38, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k1_tarski(B_31))=A_30 | r2_hidden(B_31, A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.74/2.50  tff(c_270, plain, (![A_67, C_68, B_69]: (r1_xboole_0(A_67, k4_xboole_0(C_68, B_69)) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.74/2.50  tff(c_4287, plain, (![A_197, A_198, B_199]: (r1_xboole_0(A_197, A_198) | ~r1_tarski(A_197, k1_tarski(B_199)) | r2_hidden(B_199, A_198))), inference(superposition, [status(thm), theory('equality')], [c_38, c_270])).
% 6.74/2.50  tff(c_4309, plain, (![A_198]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_198) | r2_hidden('#skF_6', A_198))), inference(resolution, [status(thm)], [c_47, c_4287])).
% 6.74/2.50  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.74/2.50  tff(c_26, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.74/2.50  tff(c_1278, plain, (![A_132, C_133, B_134]: (k4_xboole_0(A_132, k4_xboole_0(C_133, B_134))=A_132 | ~r1_tarski(A_132, B_134))), inference(resolution, [status(thm)], [c_270, c_26])).
% 6.74/2.50  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.74/2.50  tff(c_1429, plain, (![C_137, B_138]: (k3_xboole_0(C_137, B_138)=C_137 | ~r1_tarski(C_137, B_138))), inference(superposition, [status(thm), theory('equality')], [c_1278, c_18])).
% 6.74/2.50  tff(c_2259, plain, (![A_158, B_159]: (k3_xboole_0(k4_xboole_0(A_158, B_159), A_158)=k4_xboole_0(A_158, B_159))), inference(resolution, [status(thm)], [c_16, c_1429])).
% 6.74/2.50  tff(c_2321, plain, (![A_158, B_159]: (k3_xboole_0(A_158, k4_xboole_0(A_158, B_159))=k4_xboole_0(A_158, B_159))), inference(superposition, [status(thm), theory('equality')], [c_2259, c_2])).
% 6.74/2.50  tff(c_179, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.74/2.50  tff(c_182, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k3_xboole_0(A_55, k4_xboole_0(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_18])).
% 6.74/2.50  tff(c_3854, plain, (![A_190, B_191]: (k4_xboole_0(A_190, k3_xboole_0(A_190, B_191))=k4_xboole_0(A_190, B_191))), inference(demodulation, [status(thm), theory('equality')], [c_2321, c_182])).
% 6.74/2.50  tff(c_3965, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3854])).
% 6.74/2.50  tff(c_264, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), B_66) | r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.74/2.50  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.74/2.50  tff(c_769, plain, (![A_93, B_94, A_95]: (~r1_xboole_0(A_93, B_94) | r1_xboole_0(A_95, k3_xboole_0(A_93, B_94)))), inference(resolution, [status(thm)], [c_264, c_14])).
% 6.74/2.50  tff(c_6609, plain, (![A_263, A_264, B_265]: (k4_xboole_0(A_263, k3_xboole_0(A_264, B_265))=A_263 | ~r1_xboole_0(A_264, B_265))), inference(resolution, [status(thm)], [c_769, c_26])).
% 6.74/2.50  tff(c_7950, plain, (![B_295, A_296]: (k4_xboole_0(B_295, A_296)=B_295 | ~r1_xboole_0(A_296, B_295))), inference(superposition, [status(thm), theory('equality')], [c_3965, c_6609])).
% 6.74/2.50  tff(c_8435, plain, (![A_303]: (k4_xboole_0(A_303, k3_xboole_0('#skF_4', '#skF_3'))=A_303 | r2_hidden('#skF_6', A_303))), inference(resolution, [status(thm)], [c_4309, c_7950])).
% 6.74/2.50  tff(c_3581, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(demodulation, [status(thm), theory('equality')], [c_2321, c_182])).
% 6.74/2.50  tff(c_8485, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4' | r2_hidden('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8435, c_3581])).
% 6.74/2.50  tff(c_8568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_761, c_4586, c_8485])).
% 6.74/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.74/2.50  
% 6.74/2.50  Inference rules
% 6.74/2.50  ----------------------
% 6.74/2.50  #Ref     : 0
% 6.74/2.50  #Sup     : 2126
% 6.74/2.50  #Fact    : 0
% 6.74/2.50  #Define  : 0
% 6.74/2.50  #Split   : 3
% 6.74/2.50  #Chain   : 0
% 6.74/2.50  #Close   : 0
% 6.74/2.50  
% 6.74/2.50  Ordering : KBO
% 6.74/2.50  
% 6.74/2.50  Simplification rules
% 6.74/2.50  ----------------------
% 6.74/2.50  #Subsume      : 330
% 6.74/2.50  #Demod        : 1297
% 6.74/2.50  #Tautology    : 873
% 6.74/2.50  #SimpNegUnit  : 75
% 6.74/2.50  #BackRed      : 49
% 6.74/2.50  
% 6.74/2.50  #Partial instantiations: 0
% 6.74/2.50  #Strategies tried      : 1
% 6.74/2.50  
% 6.74/2.50  Timing (in seconds)
% 6.74/2.50  ----------------------
% 6.74/2.51  Preprocessing        : 0.32
% 6.74/2.51  Parsing              : 0.18
% 6.74/2.51  CNF conversion       : 0.02
% 6.74/2.51  Main loop            : 1.37
% 6.74/2.51  Inferencing          : 0.39
% 6.74/2.51  Reduction            : 0.55
% 6.74/2.51  Demodulation         : 0.43
% 6.74/2.51  BG Simplification    : 0.04
% 6.74/2.51  Subsumption          : 0.30
% 6.74/2.51  Abstraction          : 0.06
% 6.74/2.51  MUC search           : 0.00
% 6.74/2.51  Cooper               : 0.00
% 6.74/2.51  Total                : 1.73
% 6.74/2.51  Index Insertion      : 0.00
% 6.74/2.51  Index Deletion       : 0.00
% 6.74/2.51  Index Matching       : 0.00
% 6.74/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
