%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:01 EST 2020

% Result     : Theorem 9.36s
% Output     : CNFRefutation 9.50s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 155 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  112 ( 282 expanded)
%              Number of equality atoms :    9 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),k3_xboole_0(A_13,B_14))
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_174,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_185,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_174])).

tff(c_396,plain,(
    ! [D_73,B_74,A_75] :
      ( r2_hidden(D_73,B_74)
      | ~ r2_hidden(D_73,k3_xboole_0(A_75,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5563,plain,(
    ! [D_209] :
      ( r2_hidden(D_209,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_209,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_396])).

tff(c_5604,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),k1_tarski('#skF_7'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_5563])).

tff(c_9786,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5604])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9792,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_9786,c_24])).

tff(c_56,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_152,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,A_51)
      | ~ r1_xboole_0(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_155,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_152])).

tff(c_1594,plain,(
    ! [A_126,C_127,B_128] :
      ( ~ r1_xboole_0(A_126,C_127)
      | ~ r1_xboole_0(A_126,B_128)
      | r1_xboole_0(A_126,k2_xboole_0(B_128,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14454,plain,(
    ! [B_306,C_307,A_308] :
      ( r1_xboole_0(k2_xboole_0(B_306,C_307),A_308)
      | ~ r1_xboole_0(A_308,C_307)
      | ~ r1_xboole_0(A_308,B_306) ) ),
    inference(resolution,[status(thm)],[c_1594,c_24])).

tff(c_54,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14469,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_14454,c_54])).

tff(c_14513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_155,c_14469])).

tff(c_14515,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_5604])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1016,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_3'(A_111,B_112),k3_xboole_0(A_111,B_112))
      | r1_xboole_0(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15635,plain,(
    ! [B_326,A_327] :
      ( r2_hidden('#skF_3'(B_326,A_327),k3_xboole_0(A_327,B_326))
      | r1_xboole_0(B_326,A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1016])).

tff(c_399,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_73,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_396])).

tff(c_15729,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_4'),k1_tarski('#skF_7'))
    | r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_15635,c_399])).

tff(c_15734,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15729])).

tff(c_15738,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_15734,c_24])).

tff(c_15743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14515,c_15738])).

tff(c_15745,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_15729])).

tff(c_1046,plain,(
    ! [B_4,A_3] :
      ( r2_hidden('#skF_3'(B_4,A_3),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(B_4,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1016])).

tff(c_58,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    ! [A_23,B_24] : r1_tarski(k3_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_187,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,B_59) = B_59
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_199,plain,(
    ! [A_23,B_24] : k2_xboole_0(k3_xboole_0(A_23,B_24),A_23) = A_23 ),
    inference(resolution,[status(thm)],[c_34,c_187])).

tff(c_52,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_443,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_xboole_0(A_82,B_83)
      | ~ r1_xboole_0(A_82,k2_xboole_0(B_83,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5677,plain,(
    ! [A_214,B_215,C_216] :
      ( r1_xboole_0(k1_tarski(A_214),B_215)
      | r2_hidden(A_214,k2_xboole_0(B_215,C_216)) ) ),
    inference(resolution,[status(thm)],[c_52,c_443])).

tff(c_6856,plain,(
    ! [A_235,A_236,B_237] :
      ( r1_xboole_0(k1_tarski(A_235),k3_xboole_0(A_236,B_237))
      | r2_hidden(A_235,A_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_5677])).

tff(c_6917,plain,(
    ! [A_235,A_3,B_4] :
      ( r1_xboole_0(k1_tarski(A_235),k3_xboole_0(A_3,B_4))
      | r2_hidden(A_235,B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6856])).

tff(c_406,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_480,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,k3_xboole_0(B_86,A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_406])).

tff(c_483,plain,(
    ! [C_87] :
      ( ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5'))
      | ~ r2_hidden(C_87,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_480])).

tff(c_17137,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_17169,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_6917,c_17137])).

tff(c_1784,plain,(
    ! [D_139,A_140,B_141] :
      ( r2_hidden(D_139,k3_xboole_0(A_140,B_141))
      | ~ r2_hidden(D_139,B_141)
      | ~ r2_hidden(D_139,A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_13,B_14,C_17] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_17,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5488,plain,(
    ! [A_204,B_205,D_206] :
      ( ~ r1_xboole_0(A_204,B_205)
      | ~ r2_hidden(D_206,B_205)
      | ~ r2_hidden(D_206,A_204) ) ),
    inference(resolution,[status(thm)],[c_1784,c_28])).

tff(c_5529,plain,(
    ! [D_206] :
      ( ~ r2_hidden(D_206,'#skF_6')
      | ~ r2_hidden(D_206,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_155,c_5488])).

tff(c_17180,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_17169,c_5529])).

tff(c_17184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_17180])).

tff(c_17187,plain,(
    ! [C_340] : ~ r2_hidden(C_340,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_17191,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1046,c_17187])).

tff(c_17235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15745,c_17191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.36/3.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.36/3.66  
% 9.36/3.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 9.46/3.66  
% 9.46/3.66  %Foreground sorts:
% 9.46/3.66  
% 9.46/3.66  
% 9.46/3.66  %Background operators:
% 9.46/3.66  
% 9.46/3.66  
% 9.46/3.66  %Foreground operators:
% 9.46/3.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.46/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.46/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.46/3.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.46/3.66  tff('#skF_7', type, '#skF_7': $i).
% 9.46/3.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.46/3.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.46/3.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.46/3.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.46/3.66  tff('#skF_5', type, '#skF_5': $i).
% 9.46/3.66  tff('#skF_6', type, '#skF_6': $i).
% 9.46/3.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.46/3.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.46/3.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.46/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.46/3.66  tff('#skF_4', type, '#skF_4': $i).
% 9.46/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.46/3.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.46/3.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.46/3.66  
% 9.50/3.68  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.50/3.68  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 9.50/3.68  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.50/3.68  tff(f_38, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.50/3.68  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.50/3.68  tff(f_84, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 9.50/3.68  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.50/3.68  tff(f_64, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.50/3.68  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.50/3.68  tff(f_99, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.50/3.68  tff(c_26, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), k3_xboole_0(A_13, B_14)) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.50/3.68  tff(c_60, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.50/3.68  tff(c_174, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.50/3.68  tff(c_185, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_174])).
% 9.50/3.68  tff(c_396, plain, (![D_73, B_74, A_75]: (r2_hidden(D_73, B_74) | ~r2_hidden(D_73, k3_xboole_0(A_75, B_74)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.50/3.68  tff(c_5563, plain, (![D_209]: (r2_hidden(D_209, k1_tarski('#skF_7')) | ~r2_hidden(D_209, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_185, c_396])).
% 9.50/3.68  tff(c_5604, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), k1_tarski('#skF_7')) | r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_5563])).
% 9.50/3.68  tff(c_9786, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_5604])).
% 9.50/3.68  tff(c_24, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.50/3.68  tff(c_9792, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_9786, c_24])).
% 9.50/3.68  tff(c_56, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.50/3.68  tff(c_152, plain, (![B_50, A_51]: (r1_xboole_0(B_50, A_51) | ~r1_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.50/3.68  tff(c_155, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_152])).
% 9.50/3.68  tff(c_1594, plain, (![A_126, C_127, B_128]: (~r1_xboole_0(A_126, C_127) | ~r1_xboole_0(A_126, B_128) | r1_xboole_0(A_126, k2_xboole_0(B_128, C_127)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.50/3.68  tff(c_14454, plain, (![B_306, C_307, A_308]: (r1_xboole_0(k2_xboole_0(B_306, C_307), A_308) | ~r1_xboole_0(A_308, C_307) | ~r1_xboole_0(A_308, B_306))), inference(resolution, [status(thm)], [c_1594, c_24])).
% 9.50/3.68  tff(c_54, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.50/3.68  tff(c_14469, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_14454, c_54])).
% 9.50/3.68  tff(c_14513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9792, c_155, c_14469])).
% 9.50/3.68  tff(c_14515, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_5604])).
% 9.50/3.68  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.50/3.68  tff(c_1016, plain, (![A_111, B_112]: (r2_hidden('#skF_3'(A_111, B_112), k3_xboole_0(A_111, B_112)) | r1_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.50/3.68  tff(c_15635, plain, (![B_326, A_327]: (r2_hidden('#skF_3'(B_326, A_327), k3_xboole_0(A_327, B_326)) | r1_xboole_0(B_326, A_327))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1016])).
% 9.50/3.68  tff(c_399, plain, (![D_73]: (r2_hidden(D_73, k1_tarski('#skF_7')) | ~r2_hidden(D_73, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_185, c_396])).
% 9.50/3.68  tff(c_15729, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4'), k1_tarski('#skF_7')) | r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_15635, c_399])).
% 9.50/3.68  tff(c_15734, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_15729])).
% 9.50/3.68  tff(c_15738, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_15734, c_24])).
% 9.50/3.68  tff(c_15743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14515, c_15738])).
% 9.50/3.68  tff(c_15745, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_15729])).
% 9.50/3.68  tff(c_1046, plain, (![B_4, A_3]: (r2_hidden('#skF_3'(B_4, A_3), k3_xboole_0(A_3, B_4)) | r1_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1016])).
% 9.50/3.68  tff(c_58, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.50/3.68  tff(c_34, plain, (![A_23, B_24]: (r1_tarski(k3_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.50/3.68  tff(c_187, plain, (![A_58, B_59]: (k2_xboole_0(A_58, B_59)=B_59 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.50/3.68  tff(c_199, plain, (![A_23, B_24]: (k2_xboole_0(k3_xboole_0(A_23, B_24), A_23)=A_23)), inference(resolution, [status(thm)], [c_34, c_187])).
% 9.50/3.68  tff(c_52, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.50/3.68  tff(c_443, plain, (![A_82, B_83, C_84]: (r1_xboole_0(A_82, B_83) | ~r1_xboole_0(A_82, k2_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.50/3.68  tff(c_5677, plain, (![A_214, B_215, C_216]: (r1_xboole_0(k1_tarski(A_214), B_215) | r2_hidden(A_214, k2_xboole_0(B_215, C_216)))), inference(resolution, [status(thm)], [c_52, c_443])).
% 9.50/3.68  tff(c_6856, plain, (![A_235, A_236, B_237]: (r1_xboole_0(k1_tarski(A_235), k3_xboole_0(A_236, B_237)) | r2_hidden(A_235, A_236))), inference(superposition, [status(thm), theory('equality')], [c_199, c_5677])).
% 9.50/3.68  tff(c_6917, plain, (![A_235, A_3, B_4]: (r1_xboole_0(k1_tarski(A_235), k3_xboole_0(A_3, B_4)) | r2_hidden(A_235, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_6856])).
% 9.50/3.68  tff(c_406, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.50/3.68  tff(c_480, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(B_86, A_85)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_406])).
% 9.50/3.68  tff(c_483, plain, (![C_87]: (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5')) | ~r2_hidden(C_87, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_185, c_480])).
% 9.50/3.68  tff(c_17137, plain, (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_483])).
% 9.50/3.68  tff(c_17169, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_6917, c_17137])).
% 9.50/3.68  tff(c_1784, plain, (![D_139, A_140, B_141]: (r2_hidden(D_139, k3_xboole_0(A_140, B_141)) | ~r2_hidden(D_139, B_141) | ~r2_hidden(D_139, A_140))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.50/3.68  tff(c_28, plain, (![A_13, B_14, C_17]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_17, k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.50/3.68  tff(c_5488, plain, (![A_204, B_205, D_206]: (~r1_xboole_0(A_204, B_205) | ~r2_hidden(D_206, B_205) | ~r2_hidden(D_206, A_204))), inference(resolution, [status(thm)], [c_1784, c_28])).
% 9.50/3.68  tff(c_5529, plain, (![D_206]: (~r2_hidden(D_206, '#skF_6') | ~r2_hidden(D_206, '#skF_5'))), inference(resolution, [status(thm)], [c_155, c_5488])).
% 9.50/3.68  tff(c_17180, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_17169, c_5529])).
% 9.50/3.68  tff(c_17184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_17180])).
% 9.50/3.68  tff(c_17187, plain, (![C_340]: (~r2_hidden(C_340, k3_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_483])).
% 9.50/3.68  tff(c_17191, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1046, c_17187])).
% 9.50/3.68  tff(c_17235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15745, c_17191])).
% 9.50/3.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.50/3.68  
% 9.50/3.68  Inference rules
% 9.50/3.68  ----------------------
% 9.50/3.68  #Ref     : 0
% 9.50/3.68  #Sup     : 4310
% 9.50/3.68  #Fact    : 0
% 9.50/3.68  #Define  : 0
% 9.50/3.68  #Split   : 4
% 9.50/3.68  #Chain   : 0
% 9.50/3.68  #Close   : 0
% 9.50/3.68  
% 9.50/3.68  Ordering : KBO
% 9.50/3.68  
% 9.50/3.68  Simplification rules
% 9.50/3.68  ----------------------
% 9.50/3.68  #Subsume      : 483
% 9.50/3.68  #Demod        : 4091
% 9.50/3.68  #Tautology    : 2003
% 9.50/3.68  #SimpNegUnit  : 15
% 9.50/3.68  #BackRed      : 6
% 9.50/3.68  
% 9.50/3.68  #Partial instantiations: 0
% 9.50/3.68  #Strategies tried      : 1
% 9.50/3.68  
% 9.50/3.68  Timing (in seconds)
% 9.50/3.68  ----------------------
% 9.50/3.68  Preprocessing        : 0.31
% 9.50/3.68  Parsing              : 0.16
% 9.50/3.68  CNF conversion       : 0.02
% 9.50/3.68  Main loop            : 2.46
% 9.50/3.68  Inferencing          : 0.49
% 9.50/3.68  Reduction            : 1.34
% 9.50/3.68  Demodulation         : 1.18
% 9.50/3.68  BG Simplification    : 0.06
% 9.50/3.68  Subsumption          : 0.41
% 9.50/3.68  Abstraction          : 0.09
% 9.50/3.68  MUC search           : 0.00
% 9.50/3.68  Cooper               : 0.00
% 9.50/3.68  Total                : 2.81
% 9.50/3.68  Index Insertion      : 0.00
% 9.50/3.68  Index Deletion       : 0.00
% 9.50/3.68  Index Matching       : 0.00
% 9.50/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
