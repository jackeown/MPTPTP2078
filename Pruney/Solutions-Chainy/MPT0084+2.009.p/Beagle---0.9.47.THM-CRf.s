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
% DateTime   : Thu Dec  3 09:44:05 EST 2020

% Result     : Theorem 14.35s
% Output     : CNFRefutation 14.35s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 116 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 176 expanded)
%              Number of equality atoms :   22 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(c_16,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_29,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_89,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_89])).

tff(c_132,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135,plain,(
    ! [C_39] :
      ( ~ r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
      | ~ r2_hidden(C_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_132])).

tff(c_143,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_135])).

tff(c_114,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_145,plain,(
    ! [A_41] : k4_xboole_0(A_41,A_41) = k3_xboole_0(A_41,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_114])).

tff(c_155,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_16])).

tff(c_492,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(A_61,B_62),k3_xboole_0(A_61,B_62))
      | r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_501,plain,
    ( r2_hidden('#skF_1'(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_492])).

tff(c_513,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_501])).

tff(c_20,plain,(
    ! [A_19,C_21,B_20] :
      ( r1_xboole_0(A_19,C_21)
      | ~ r1_xboole_0(B_20,C_21)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1126,plain,(
    ! [A_82] :
      ( r1_xboole_0(A_82,k1_xboole_0)
      | ~ r1_tarski(A_82,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_513,c_20])).

tff(c_178,plain,(
    ! [A_42,B_43] :
      ( ~ r1_xboole_0(k3_xboole_0(A_42,B_43),B_43)
      | r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_191,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_1132,plain,(
    ! [A_1] :
      ( r1_xboole_0(A_1,k1_xboole_0)
      | ~ r1_tarski(k3_xboole_0(k1_xboole_0,A_1),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1126,c_191])).

tff(c_1186,plain,(
    ! [A_86] : r1_xboole_0(A_86,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1132])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1243,plain,(
    ! [A_89] : k3_xboole_0(A_89,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1186,c_4])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_117,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,k4_xboole_0(A_35,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_18])).

tff(c_1252,plain,(
    ! [A_89] : k3_xboole_0(A_89,k4_xboole_0(A_89,k1_xboole_0)) = k4_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1243,c_117])).

tff(c_1358,plain,(
    ! [A_92] : k3_xboole_0(A_92,A_92) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_1252])).

tff(c_40,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [B_27,A_28] : r1_tarski(k3_xboole_0(B_27,A_28),A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_12])).

tff(c_1403,plain,(
    ! [A_92] : r1_tarski(A_92,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_55])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_673,plain,(
    ! [A_64,C_65,B_66,D_67] :
      ( r1_tarski(k3_xboole_0(A_64,C_65),k3_xboole_0(B_66,D_67))
      | ~ r1_tarski(C_65,D_67)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1711,plain,(
    ! [A_102,C_103,B_104,A_105] :
      ( r1_tarski(k3_xboole_0(A_102,C_103),k3_xboole_0(B_104,A_105))
      | ~ r1_tarski(C_103,B_104)
      | ~ r1_tarski(A_102,A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_673])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_xboole_0(A_47,C_48)
      | ~ r1_xboole_0(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_218,plain,(
    ! [A_47,B_4,A_3] :
      ( r1_xboole_0(A_47,B_4)
      | ~ r1_tarski(A_47,A_3)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_213])).

tff(c_7334,plain,(
    ! [C_238,A_235,B_239,B_236,A_237] :
      ( r1_xboole_0(k3_xboole_0(A_237,C_238),B_239)
      | k3_xboole_0(k3_xboole_0(B_236,A_235),B_239) != k1_xboole_0
      | ~ r1_tarski(C_238,B_236)
      | ~ r1_tarski(A_237,A_235) ) ),
    inference(resolution,[status(thm)],[c_1711,c_218])).

tff(c_49578,plain,(
    ! [B_568,A_566,C_567,A_564,A_565] :
      ( r1_xboole_0(k3_xboole_0(A_564,C_567),A_566)
      | k3_xboole_0(A_566,k3_xboole_0(B_568,A_565)) != k1_xboole_0
      | ~ r1_tarski(C_567,B_568)
      | ~ r1_tarski(A_564,A_565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7334])).

tff(c_51178,plain,(
    ! [A_572,C_573] :
      ( r1_xboole_0(k3_xboole_0(A_572,C_573),'#skF_2')
      | ~ r1_tarski(C_573,'#skF_4')
      | ~ r1_tarski(A_572,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_49578])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( ~ r1_xboole_0(k3_xboole_0(A_22,B_23),B_23)
      | r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_51190,plain,(
    ! [A_572] :
      ( r1_xboole_0(A_572,'#skF_2')
      | ~ r1_tarski('#skF_2','#skF_4')
      | ~ r1_tarski(A_572,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_51178,c_22])).

tff(c_51396,plain,(
    ! [A_574] :
      ( r1_xboole_0(A_574,'#skF_2')
      | ~ r1_tarski(A_574,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_51190])).

tff(c_141,plain,(
    ! [B_2,A_1,C_39] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_39,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_511,plain,(
    ! [B_62,A_61] :
      ( ~ r1_xboole_0(B_62,A_61)
      | r1_xboole_0(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_492,c_141])).

tff(c_51429,plain,(
    ! [A_575] :
      ( r1_xboole_0('#skF_2',A_575)
      | ~ r1_tarski(A_575,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_51396,c_511])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_51448,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_51429,c_28])).

tff(c_51458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_51448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.35/7.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.35/7.02  
% 14.35/7.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.35/7.02  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.35/7.02  
% 14.35/7.02  %Foreground sorts:
% 14.35/7.02  
% 14.35/7.02  
% 14.35/7.02  %Background operators:
% 14.35/7.02  
% 14.35/7.02  
% 14.35/7.02  %Foreground operators:
% 14.35/7.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.35/7.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.35/7.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.35/7.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.35/7.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.35/7.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.35/7.02  tff('#skF_2', type, '#skF_2': $i).
% 14.35/7.02  tff('#skF_3', type, '#skF_3': $i).
% 14.35/7.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.35/7.02  tff('#skF_4', type, '#skF_4': $i).
% 14.35/7.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.35/7.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.35/7.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.35/7.02  
% 14.35/7.03  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.35/7.03  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 14.35/7.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.35/7.03  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 14.35/7.03  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 14.35/7.03  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 14.35/7.03  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.35/7.03  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 14.35/7.03  tff(f_69, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 14.35/7.03  tff(f_53, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 14.35/7.03  tff(c_16, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.35/7.03  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.35/7.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.35/7.03  tff(c_24, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.35/7.03  tff(c_29, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 14.35/7.03  tff(c_89, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.35/7.03  tff(c_93, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_89])).
% 14.35/7.03  tff(c_132, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.35/7.03  tff(c_135, plain, (![C_39]: (~r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden(C_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_93, c_132])).
% 14.35/7.03  tff(c_143, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_135])).
% 14.35/7.03  tff(c_114, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.35/7.03  tff(c_145, plain, (![A_41]: (k4_xboole_0(A_41, A_41)=k3_xboole_0(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_114])).
% 14.35/7.03  tff(c_155, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_145, c_16])).
% 14.35/7.03  tff(c_492, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(A_61, B_62), k3_xboole_0(A_61, B_62)) | r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.35/7.03  tff(c_501, plain, (r2_hidden('#skF_1'(k1_xboole_0, k1_xboole_0), k1_xboole_0) | r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_155, c_492])).
% 14.35/7.03  tff(c_513, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_143, c_501])).
% 14.35/7.03  tff(c_20, plain, (![A_19, C_21, B_20]: (r1_xboole_0(A_19, C_21) | ~r1_xboole_0(B_20, C_21) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.35/7.03  tff(c_1126, plain, (![A_82]: (r1_xboole_0(A_82, k1_xboole_0) | ~r1_tarski(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_513, c_20])).
% 14.35/7.03  tff(c_178, plain, (![A_42, B_43]: (~r1_xboole_0(k3_xboole_0(A_42, B_43), B_43) | r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.35/7.03  tff(c_191, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 14.35/7.03  tff(c_1132, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0) | ~r1_tarski(k3_xboole_0(k1_xboole_0, A_1), k1_xboole_0))), inference(resolution, [status(thm)], [c_1126, c_191])).
% 14.35/7.03  tff(c_1186, plain, (![A_86]: (r1_xboole_0(A_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1132])).
% 14.35/7.03  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.35/7.03  tff(c_1243, plain, (![A_89]: (k3_xboole_0(A_89, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1186, c_4])).
% 14.35/7.03  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.35/7.03  tff(c_117, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k3_xboole_0(A_35, k4_xboole_0(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_18])).
% 14.35/7.03  tff(c_1252, plain, (![A_89]: (k3_xboole_0(A_89, k4_xboole_0(A_89, k1_xboole_0))=k4_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1243, c_117])).
% 14.35/7.03  tff(c_1358, plain, (![A_92]: (k3_xboole_0(A_92, A_92)=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_1252])).
% 14.35/7.03  tff(c_40, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.35/7.03  tff(c_55, plain, (![B_27, A_28]: (r1_tarski(k3_xboole_0(B_27, A_28), A_28))), inference(superposition, [status(thm), theory('equality')], [c_40, c_12])).
% 14.35/7.03  tff(c_1403, plain, (![A_92]: (r1_tarski(A_92, A_92))), inference(superposition, [status(thm), theory('equality')], [c_1358, c_55])).
% 14.35/7.03  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.35/7.03  tff(c_673, plain, (![A_64, C_65, B_66, D_67]: (r1_tarski(k3_xboole_0(A_64, C_65), k3_xboole_0(B_66, D_67)) | ~r1_tarski(C_65, D_67) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.35/7.03  tff(c_1711, plain, (![A_102, C_103, B_104, A_105]: (r1_tarski(k3_xboole_0(A_102, C_103), k3_xboole_0(B_104, A_105)) | ~r1_tarski(C_103, B_104) | ~r1_tarski(A_102, A_105))), inference(superposition, [status(thm), theory('equality')], [c_2, c_673])).
% 14.35/7.03  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.35/7.03  tff(c_213, plain, (![A_47, C_48, B_49]: (r1_xboole_0(A_47, C_48) | ~r1_xboole_0(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.35/7.03  tff(c_218, plain, (![A_47, B_4, A_3]: (r1_xboole_0(A_47, B_4) | ~r1_tarski(A_47, A_3) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_213])).
% 14.35/7.03  tff(c_7334, plain, (![C_238, A_235, B_239, B_236, A_237]: (r1_xboole_0(k3_xboole_0(A_237, C_238), B_239) | k3_xboole_0(k3_xboole_0(B_236, A_235), B_239)!=k1_xboole_0 | ~r1_tarski(C_238, B_236) | ~r1_tarski(A_237, A_235))), inference(resolution, [status(thm)], [c_1711, c_218])).
% 14.35/7.03  tff(c_49578, plain, (![B_568, A_566, C_567, A_564, A_565]: (r1_xboole_0(k3_xboole_0(A_564, C_567), A_566) | k3_xboole_0(A_566, k3_xboole_0(B_568, A_565))!=k1_xboole_0 | ~r1_tarski(C_567, B_568) | ~r1_tarski(A_564, A_565))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7334])).
% 14.35/7.03  tff(c_51178, plain, (![A_572, C_573]: (r1_xboole_0(k3_xboole_0(A_572, C_573), '#skF_2') | ~r1_tarski(C_573, '#skF_4') | ~r1_tarski(A_572, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_49578])).
% 14.35/7.03  tff(c_22, plain, (![A_22, B_23]: (~r1_xboole_0(k3_xboole_0(A_22, B_23), B_23) | r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.35/7.03  tff(c_51190, plain, (![A_572]: (r1_xboole_0(A_572, '#skF_2') | ~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski(A_572, '#skF_3'))), inference(resolution, [status(thm)], [c_51178, c_22])).
% 14.35/7.03  tff(c_51396, plain, (![A_574]: (r1_xboole_0(A_574, '#skF_2') | ~r1_tarski(A_574, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_51190])).
% 14.35/7.03  tff(c_141, plain, (![B_2, A_1, C_39]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_39, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_132])).
% 14.35/7.03  tff(c_511, plain, (![B_62, A_61]: (~r1_xboole_0(B_62, A_61) | r1_xboole_0(A_61, B_62))), inference(resolution, [status(thm)], [c_492, c_141])).
% 14.35/7.03  tff(c_51429, plain, (![A_575]: (r1_xboole_0('#skF_2', A_575) | ~r1_tarski(A_575, '#skF_3'))), inference(resolution, [status(thm)], [c_51396, c_511])).
% 14.35/7.03  tff(c_28, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.35/7.03  tff(c_51448, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_51429, c_28])).
% 14.35/7.03  tff(c_51458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1403, c_51448])).
% 14.35/7.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.35/7.03  
% 14.35/7.03  Inference rules
% 14.35/7.03  ----------------------
% 14.35/7.03  #Ref     : 0
% 14.35/7.03  #Sup     : 12548
% 14.35/7.03  #Fact    : 0
% 14.35/7.03  #Define  : 0
% 14.35/7.03  #Split   : 14
% 14.35/7.03  #Chain   : 0
% 14.35/7.03  #Close   : 0
% 14.35/7.03  
% 14.35/7.03  Ordering : KBO
% 14.35/7.03  
% 14.35/7.03  Simplification rules
% 14.35/7.03  ----------------------
% 14.35/7.03  #Subsume      : 5212
% 14.35/7.03  #Demod        : 9037
% 14.35/7.03  #Tautology    : 4979
% 14.35/7.03  #SimpNegUnit  : 433
% 14.35/7.03  #BackRed      : 18
% 14.35/7.03  
% 14.35/7.03  #Partial instantiations: 0
% 14.35/7.03  #Strategies tried      : 1
% 14.35/7.03  
% 14.35/7.03  Timing (in seconds)
% 14.35/7.03  ----------------------
% 14.35/7.04  Preprocessing        : 0.27
% 14.35/7.04  Parsing              : 0.16
% 14.35/7.04  CNF conversion       : 0.02
% 14.35/7.04  Main loop            : 6.04
% 14.35/7.04  Inferencing          : 0.92
% 14.35/7.04  Reduction            : 3.16
% 14.35/7.04  Demodulation         : 2.63
% 14.35/7.04  BG Simplification    : 0.09
% 14.35/7.04  Subsumption          : 1.64
% 14.35/7.04  Abstraction          : 0.15
% 14.35/7.04  MUC search           : 0.00
% 14.35/7.04  Cooper               : 0.00
% 14.35/7.04  Total                : 6.35
% 14.35/7.04  Index Insertion      : 0.00
% 14.35/7.04  Index Deletion       : 0.00
% 14.35/7.04  Index Matching       : 0.00
% 14.35/7.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
