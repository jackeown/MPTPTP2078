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
% DateTime   : Thu Dec  3 09:44:07 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 127 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 175 expanded)
%              Number of equality atoms :   34 (  68 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_235,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(A_43,B_44)
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_241,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_235,c_36])).

tff(c_244,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_241])).

tff(c_18,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_304,plain,(
    ! [A_50,B_51] : k2_xboole_0(k3_xboole_0(A_50,B_51),k4_xboole_0(A_50,B_51)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_331,plain,(
    ! [A_52] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_52,k1_xboole_0)) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_304])).

tff(c_45,plain,(
    ! [A_28,B_29] : r1_tarski(k3_xboole_0(A_28,B_29),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_45])).

tff(c_178,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_48,c_178])).

tff(c_340,plain,(
    ! [A_52] : k4_xboole_0(A_52,k1_xboole_0) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_192])).

tff(c_645,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_680,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k3_xboole_0(A_52,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_645])).

tff(c_756,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_680])).

tff(c_22,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_761,plain,(
    ! [A_78] : k4_xboole_0(A_78,k1_xboole_0) = k3_xboole_0(A_78,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_22])).

tff(c_782,plain,(
    ! [A_78] : k3_xboole_0(A_78,A_78) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_761])).

tff(c_32,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_37,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_141,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_141])).

tff(c_514,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_517,plain,(
    ! [C_68] :
      ( ~ r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
      | ~ r2_hidden(C_68,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_514])).

tff(c_531,plain,(
    ! [C_68] : ~ r2_hidden(C_68,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_517])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1477,plain,(
    ! [A_105,B_106,C_107] :
      ( ~ r1_xboole_0(A_105,B_106)
      | ~ r2_hidden(C_107,k3_xboole_0(B_106,A_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_514])).

tff(c_1513,plain,(
    ! [B_108,A_109] :
      ( ~ r1_xboole_0(B_108,A_109)
      | r1_xboole_0(A_109,B_108) ) ),
    inference(resolution,[status(thm)],[c_8,c_1477])).

tff(c_1542,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_37,c_1513])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1550,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1542,c_4])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k3_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k3_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1576,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1550,c_14])).

tff(c_1672,plain,
    ( r2_hidden('#skF_1'('#skF_4',k3_xboole_0('#skF_3','#skF_2')),k1_xboole_0)
    | r1_xboole_0('#skF_4',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1576,c_8])).

tff(c_1706,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_531,c_1672])).

tff(c_1508,plain,(
    ! [B_6,A_5] :
      ( ~ r1_xboole_0(B_6,A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_1477])).

tff(c_1722,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1706,c_1508])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_194,plain,(
    k2_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_178])).

tff(c_286,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_xboole_0(A_47,B_48)
      | ~ r1_xboole_0(A_47,k2_xboole_0(B_48,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_365,plain,(
    ! [A_54] :
      ( r1_xboole_0(A_54,'#skF_2')
      | ~ r1_xboole_0(A_54,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_286])).

tff(c_369,plain,(
    ! [A_54] :
      ( k3_xboole_0(A_54,'#skF_2') = k1_xboole_0
      | ~ r1_xboole_0(A_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_365,c_4])).

tff(c_1742,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1722,c_369])).

tff(c_2079,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1742,c_14])).

tff(c_2135,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_2079])).

tff(c_2137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_2135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:37:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.63  
% 3.47/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.47/1.63  
% 3.47/1.63  %Foreground sorts:
% 3.47/1.63  
% 3.47/1.63  
% 3.47/1.63  %Background operators:
% 3.47/1.63  
% 3.47/1.63  
% 3.47/1.63  %Foreground operators:
% 3.47/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.47/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.47/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.47/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.64  
% 3.47/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.47/1.65  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.47/1.65  tff(f_86, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.47/1.65  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.47/1.65  tff(f_61, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.47/1.65  tff(f_53, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.47/1.65  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.47/1.65  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.47/1.65  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.47/1.65  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.47/1.65  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.47/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.47/1.65  tff(c_235, plain, (![A_43, B_44]: (r1_xboole_0(A_43, B_44) | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.65  tff(c_36, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.47/1.65  tff(c_241, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_235, c_36])).
% 3.47/1.65  tff(c_244, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_241])).
% 3.47/1.65  tff(c_18, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.47/1.65  tff(c_304, plain, (![A_50, B_51]: (k2_xboole_0(k3_xboole_0(A_50, B_51), k4_xboole_0(A_50, B_51))=A_50)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.65  tff(c_331, plain, (![A_52]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_52, k1_xboole_0))=A_52)), inference(superposition, [status(thm), theory('equality')], [c_18, c_304])).
% 3.47/1.65  tff(c_45, plain, (![A_28, B_29]: (r1_tarski(k3_xboole_0(A_28, B_29), A_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.47/1.65  tff(c_48, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_45])).
% 3.47/1.65  tff(c_178, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.47/1.65  tff(c_192, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(resolution, [status(thm)], [c_48, c_178])).
% 3.47/1.65  tff(c_340, plain, (![A_52]: (k4_xboole_0(A_52, k1_xboole_0)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_331, c_192])).
% 3.47/1.65  tff(c_645, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.47/1.65  tff(c_680, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k3_xboole_0(A_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_340, c_645])).
% 3.47/1.65  tff(c_756, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_680])).
% 3.47/1.65  tff(c_22, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.47/1.65  tff(c_761, plain, (![A_78]: (k4_xboole_0(A_78, k1_xboole_0)=k3_xboole_0(A_78, A_78))), inference(superposition, [status(thm), theory('equality')], [c_756, c_22])).
% 3.47/1.65  tff(c_782, plain, (![A_78]: (k3_xboole_0(A_78, A_78)=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_340, c_761])).
% 3.47/1.65  tff(c_32, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.47/1.65  tff(c_37, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 3.47/1.65  tff(c_141, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.65  tff(c_145, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_141])).
% 3.47/1.65  tff(c_514, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.65  tff(c_517, plain, (![C_68]: (~r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden(C_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_145, c_514])).
% 3.47/1.65  tff(c_531, plain, (![C_68]: (~r2_hidden(C_68, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_517])).
% 3.47/1.65  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.65  tff(c_1477, plain, (![A_105, B_106, C_107]: (~r1_xboole_0(A_105, B_106) | ~r2_hidden(C_107, k3_xboole_0(B_106, A_105)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_514])).
% 3.47/1.65  tff(c_1513, plain, (![B_108, A_109]: (~r1_xboole_0(B_108, A_109) | r1_xboole_0(A_109, B_108))), inference(resolution, [status(thm)], [c_8, c_1477])).
% 3.47/1.65  tff(c_1542, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_37, c_1513])).
% 3.47/1.65  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.65  tff(c_1550, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1542, c_4])).
% 3.47/1.65  tff(c_14, plain, (![A_12, B_13, C_14]: (k3_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k3_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.47/1.65  tff(c_1576, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1550, c_14])).
% 3.47/1.65  tff(c_1672, plain, (r2_hidden('#skF_1'('#skF_4', k3_xboole_0('#skF_3', '#skF_2')), k1_xboole_0) | r1_xboole_0('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1576, c_8])).
% 3.47/1.65  tff(c_1706, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_531, c_1672])).
% 3.47/1.65  tff(c_1508, plain, (![B_6, A_5]: (~r1_xboole_0(B_6, A_5) | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_1477])).
% 3.47/1.65  tff(c_1722, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_1706, c_1508])).
% 3.47/1.65  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.47/1.65  tff(c_194, plain, (k2_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_178])).
% 3.47/1.65  tff(c_286, plain, (![A_47, B_48, C_49]: (r1_xboole_0(A_47, B_48) | ~r1_xboole_0(A_47, k2_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.47/1.65  tff(c_365, plain, (![A_54]: (r1_xboole_0(A_54, '#skF_2') | ~r1_xboole_0(A_54, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_286])).
% 3.47/1.65  tff(c_369, plain, (![A_54]: (k3_xboole_0(A_54, '#skF_2')=k1_xboole_0 | ~r1_xboole_0(A_54, '#skF_4'))), inference(resolution, [status(thm)], [c_365, c_4])).
% 3.47/1.65  tff(c_1742, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1722, c_369])).
% 3.47/1.65  tff(c_2079, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1742, c_14])).
% 3.47/1.65  tff(c_2135, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_782, c_2079])).
% 3.47/1.65  tff(c_2137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_2135])).
% 3.47/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.65  
% 3.47/1.65  Inference rules
% 3.47/1.65  ----------------------
% 3.47/1.65  #Ref     : 0
% 3.47/1.65  #Sup     : 531
% 3.47/1.65  #Fact    : 0
% 3.47/1.65  #Define  : 0
% 3.47/1.65  #Split   : 2
% 3.47/1.65  #Chain   : 0
% 3.47/1.65  #Close   : 0
% 3.47/1.65  
% 3.47/1.65  Ordering : KBO
% 3.47/1.65  
% 3.47/1.65  Simplification rules
% 3.47/1.65  ----------------------
% 3.47/1.65  #Subsume      : 44
% 3.47/1.65  #Demod        : 340
% 3.47/1.65  #Tautology    : 321
% 3.47/1.65  #SimpNegUnit  : 10
% 3.47/1.65  #BackRed      : 3
% 3.47/1.65  
% 3.47/1.65  #Partial instantiations: 0
% 3.47/1.65  #Strategies tried      : 1
% 3.47/1.65  
% 3.47/1.65  Timing (in seconds)
% 3.47/1.65  ----------------------
% 3.47/1.65  Preprocessing        : 0.31
% 3.47/1.65  Parsing              : 0.18
% 3.47/1.65  CNF conversion       : 0.02
% 3.47/1.65  Main loop            : 0.54
% 3.47/1.65  Inferencing          : 0.17
% 3.47/1.65  Reduction            : 0.22
% 3.47/1.65  Demodulation         : 0.18
% 3.47/1.65  BG Simplification    : 0.02
% 3.47/1.65  Subsumption          : 0.09
% 3.47/1.65  Abstraction          : 0.02
% 3.47/1.65  MUC search           : 0.00
% 3.47/1.66  Cooper               : 0.00
% 3.47/1.66  Total                : 0.88
% 3.47/1.66  Index Insertion      : 0.00
% 3.47/1.66  Index Deletion       : 0.00
% 3.47/1.66  Index Matching       : 0.00
% 3.47/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
