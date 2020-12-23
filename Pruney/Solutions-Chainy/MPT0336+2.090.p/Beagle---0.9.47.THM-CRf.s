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
% DateTime   : Thu Dec  3 09:55:12 EST 2020

% Result     : Theorem 6.50s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 181 expanded)
%              Number of equality atoms :   11 (  23 expanded)
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

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_117,negated_conjecture,(
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

tff(f_108,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),k3_xboole_0(A_10,B_11))
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_390,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r2_hidden(C_89,B_88)
      | ~ r2_hidden(C_89,A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_415,plain,(
    ! [C_90] :
      ( ~ r2_hidden(C_90,'#skF_4')
      | ~ r2_hidden(C_90,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_390])).

tff(c_429,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_415])).

tff(c_42,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,k1_tarski(B_37)) = A_36
      | r2_hidden(B_37,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_102,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(A_43,B_44)
      | k4_xboole_0(A_43,B_44) != A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [B_44,A_43] :
      ( r1_xboole_0(B_44,A_43)
      | k4_xboole_0(A_43,B_44) != A_43 ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_168,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | r1_xboole_0(A_56,k3_xboole_0(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_181,plain,(
    ! [B_57,C_58,A_56] :
      ( r1_xboole_0(k3_xboole_0(B_57,C_58),A_56)
      | ~ r1_xboole_0(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_168,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_51,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_110,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_114,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_110])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_249,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_340,plain,(
    ! [A_81,B_82,A_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | r1_xboole_0(A_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(resolution,[status(thm)],[c_8,c_249])).

tff(c_351,plain,(
    ! [A_83] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6'))
      | r1_xboole_0(A_83,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_340])).

tff(c_2972,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_2993,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_181,c_2972])).

tff(c_3027,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_6')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_108,c_2993])).

tff(c_3044,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3027])).

tff(c_3048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_3044])).

tff(c_3049,plain,(
    ! [A_83] : r1_xboole_0(A_83,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_317,plain,(
    ! [B_78,A_79,C_80] :
      ( ~ r1_xboole_0(B_78,A_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_79,B_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_331,plain,(
    ! [C_80] :
      ( ~ r1_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3'))
      | ~ r2_hidden(C_80,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_317])).

tff(c_3097,plain,(
    ! [C_155] : ~ r2_hidden(C_155,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3049,c_331])).

tff(c_3110,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_3097])).

tff(c_61,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_61])).

tff(c_886,plain,(
    ! [A_121,C_122,B_123] :
      ( ~ r1_xboole_0(A_121,C_122)
      | ~ r1_xboole_0(A_121,B_123)
      | r1_xboole_0(A_121,k2_xboole_0(B_123,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6166,plain,(
    ! [B_202,C_203,A_204] :
      ( r1_xboole_0(k2_xboole_0(B_202,C_203),A_204)
      | ~ r1_xboole_0(A_204,C_203)
      | ~ r1_xboole_0(A_204,B_202) ) ),
    inference(resolution,[status(thm)],[c_886,c_4])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6193,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6166,c_44])).

tff(c_6205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_64,c_6193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.50/2.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.39  
% 6.50/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.50/2.40  
% 6.50/2.40  %Foreground sorts:
% 6.50/2.40  
% 6.50/2.40  
% 6.50/2.40  %Background operators:
% 6.50/2.40  
% 6.50/2.40  
% 6.50/2.40  %Foreground operators:
% 6.50/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.50/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.50/2.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.50/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.50/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.50/2.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.50/2.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.50/2.40  tff('#skF_5', type, '#skF_5': $i).
% 6.50/2.40  tff('#skF_6', type, '#skF_6': $i).
% 6.50/2.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.50/2.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.50/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.50/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.50/2.40  tff('#skF_4', type, '#skF_4': $i).
% 6.50/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.50/2.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.50/2.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.50/2.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.50/2.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.50/2.40  
% 6.57/2.41  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.57/2.41  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.57/2.41  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.57/2.41  tff(f_108, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.57/2.41  tff(f_97, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.57/2.41  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.57/2.41  tff(f_93, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 6.57/2.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.57/2.41  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.57/2.41  tff(f_87, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.57/2.41  tff(c_12, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), k3_xboole_0(A_10, B_11)) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.57/2.41  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.57/2.41  tff(c_46, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.57/2.41  tff(c_390, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r2_hidden(C_89, B_88) | ~r2_hidden(C_89, A_87))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.57/2.41  tff(c_415, plain, (![C_90]: (~r2_hidden(C_90, '#skF_4') | ~r2_hidden(C_90, '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_390])).
% 6.57/2.41  tff(c_429, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_415])).
% 6.57/2.41  tff(c_42, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k1_tarski(B_37))=A_36 | r2_hidden(B_37, A_36))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.57/2.41  tff(c_102, plain, (![A_43, B_44]: (r1_xboole_0(A_43, B_44) | k4_xboole_0(A_43, B_44)!=A_43)), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.57/2.41  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.57/2.41  tff(c_108, plain, (![B_44, A_43]: (r1_xboole_0(B_44, A_43) | k4_xboole_0(A_43, B_44)!=A_43)), inference(resolution, [status(thm)], [c_102, c_4])).
% 6.57/2.41  tff(c_168, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | r1_xboole_0(A_56, k3_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.57/2.41  tff(c_181, plain, (![B_57, C_58, A_56]: (r1_xboole_0(k3_xboole_0(B_57, C_58), A_56) | ~r1_xboole_0(A_56, B_57))), inference(resolution, [status(thm)], [c_168, c_4])).
% 6.57/2.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.57/2.41  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.57/2.41  tff(c_51, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 6.57/2.41  tff(c_110, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.57/2.41  tff(c_114, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_110])).
% 6.57/2.41  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.57/2.41  tff(c_249, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.57/2.41  tff(c_340, plain, (![A_81, B_82, A_83]: (~r1_xboole_0(A_81, B_82) | r1_xboole_0(A_83, k3_xboole_0(A_81, B_82)))), inference(resolution, [status(thm)], [c_8, c_249])).
% 6.57/2.41  tff(c_351, plain, (![A_83]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6')) | r1_xboole_0(A_83, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_114, c_340])).
% 6.57/2.41  tff(c_2972, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_351])).
% 6.57/2.41  tff(c_2993, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_181, c_2972])).
% 6.57/2.41  tff(c_3027, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_6'))!='#skF_4'), inference(resolution, [status(thm)], [c_108, c_2993])).
% 6.57/2.41  tff(c_3044, plain, (r2_hidden('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_3027])).
% 6.57/2.41  tff(c_3048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_3044])).
% 6.57/2.41  tff(c_3049, plain, (![A_83]: (r1_xboole_0(A_83, k3_xboole_0('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_351])).
% 6.57/2.41  tff(c_317, plain, (![B_78, A_79, C_80]: (~r1_xboole_0(B_78, A_79) | ~r2_hidden(C_80, k3_xboole_0(A_79, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_249])).
% 6.57/2.41  tff(c_331, plain, (![C_80]: (~r1_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden(C_80, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_114, c_317])).
% 6.57/2.41  tff(c_3097, plain, (![C_155]: (~r2_hidden(C_155, k3_xboole_0('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3049, c_331])).
% 6.57/2.41  tff(c_3110, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_3097])).
% 6.57/2.41  tff(c_61, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.57/2.41  tff(c_64, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_61])).
% 6.57/2.41  tff(c_886, plain, (![A_121, C_122, B_123]: (~r1_xboole_0(A_121, C_122) | ~r1_xboole_0(A_121, B_123) | r1_xboole_0(A_121, k2_xboole_0(B_123, C_122)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.57/2.41  tff(c_6166, plain, (![B_202, C_203, A_204]: (r1_xboole_0(k2_xboole_0(B_202, C_203), A_204) | ~r1_xboole_0(A_204, C_203) | ~r1_xboole_0(A_204, B_202))), inference(resolution, [status(thm)], [c_886, c_4])).
% 6.57/2.41  tff(c_44, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.57/2.41  tff(c_6193, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6166, c_44])).
% 6.57/2.41  tff(c_6205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3110, c_64, c_6193])).
% 6.57/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/2.41  
% 6.57/2.41  Inference rules
% 6.57/2.41  ----------------------
% 6.57/2.41  #Ref     : 0
% 6.57/2.41  #Sup     : 1606
% 6.57/2.41  #Fact    : 0
% 6.57/2.41  #Define  : 0
% 6.57/2.41  #Split   : 5
% 6.57/2.41  #Chain   : 0
% 6.57/2.41  #Close   : 0
% 6.57/2.41  
% 6.57/2.41  Ordering : KBO
% 6.57/2.41  
% 6.57/2.41  Simplification rules
% 6.57/2.41  ----------------------
% 6.57/2.41  #Subsume      : 247
% 6.57/2.41  #Demod        : 916
% 6.57/2.41  #Tautology    : 576
% 6.57/2.41  #SimpNegUnit  : 27
% 6.57/2.41  #BackRed      : 10
% 6.57/2.41  
% 6.57/2.41  #Partial instantiations: 0
% 6.57/2.41  #Strategies tried      : 1
% 6.57/2.41  
% 6.57/2.42  Timing (in seconds)
% 6.57/2.42  ----------------------
% 6.57/2.42  Preprocessing        : 0.33
% 6.57/2.42  Parsing              : 0.18
% 6.57/2.42  CNF conversion       : 0.02
% 6.57/2.42  Main loop            : 1.31
% 6.57/2.42  Inferencing          : 0.35
% 6.57/2.42  Reduction            : 0.60
% 6.57/2.42  Demodulation         : 0.50
% 6.57/2.42  BG Simplification    : 0.04
% 6.57/2.42  Subsumption          : 0.23
% 6.57/2.42  Abstraction          : 0.05
% 6.57/2.42  MUC search           : 0.00
% 6.57/2.42  Cooper               : 0.00
% 6.57/2.42  Total                : 1.68
% 6.57/2.42  Index Insertion      : 0.00
% 6.57/2.42  Index Deletion       : 0.00
% 6.57/2.42  Index Matching       : 0.00
% 6.57/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
