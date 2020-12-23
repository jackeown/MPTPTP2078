%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:20 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 169 expanded)
%              Number of leaves         :   29 (  69 expanded)
%              Depth                    :   21
%              Number of atoms          :  102 ( 296 expanded)
%              Number of equality atoms :   31 (  58 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_59,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_83,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_89,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_44,plain,(
    ~ r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_145,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_148,plain,(
    r1_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_145])).

tff(c_34,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_5'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_198,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_213,plain,(
    ! [A_48,B_49] :
      ( ~ r1_xboole_0(A_48,B_49)
      | k3_xboole_0(A_48,B_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_198])).

tff(c_220,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_148,c_213])).

tff(c_32,plain,(
    ! [A_16,B_17,C_20] :
      ( ~ r1_xboole_0(A_16,B_17)
      | ~ r2_hidden(C_20,k3_xboole_0(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_225,plain,(
    ! [C_20] :
      ( ~ r1_xboole_0('#skF_8','#skF_7')
      | ~ r2_hidden(C_20,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_32])).

tff(c_232,plain,(
    ! [C_20] : ~ r2_hidden(C_20,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_225])).

tff(c_234,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_225])).

tff(c_246,plain,(
    ! [B_51] : r1_xboole_0(k1_xboole_0,B_51) ),
    inference(resolution,[status(thm)],[c_28,c_234])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_268,plain,(
    ! [B_55] : r1_xboole_0(B_55,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_246,c_22])).

tff(c_211,plain,(
    ! [A_45,B_46] :
      ( ~ r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_198])).

tff(c_274,plain,(
    ! [B_55] : k3_xboole_0(B_55,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_211])).

tff(c_345,plain,(
    ! [B_57] : k3_xboole_0(B_57,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_211])).

tff(c_42,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_700,plain,(
    ! [B_72] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_72,k1_xboole_0)) = B_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_42])).

tff(c_59,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_75,plain,(
    ! [A_33] : k2_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_36])).

tff(c_732,plain,(
    ! [B_73] : k4_xboole_0(B_73,k1_xboole_0) = B_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_75])).

tff(c_40,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_751,plain,(
    ! [B_73] : k4_xboole_0(B_73,B_73) = k3_xboole_0(B_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_40])).

tff(c_762,plain,(
    ! [B_73] : k4_xboole_0(B_73,B_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_751])).

tff(c_48,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_154,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_158,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_154])).

tff(c_163,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1844,plain,(
    ! [A_143,B_144] : k4_xboole_0(A_143,k3_xboole_0(A_143,B_144)) = k3_xboole_0(A_143,k4_xboole_0(A_143,B_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_40])).

tff(c_1918,plain,(
    k3_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_7')) = k4_xboole_0('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_1844])).

tff(c_1931,plain,(
    k3_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_1918])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),k3_xboole_0(A_16,B_17))
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1959,plain,
    ( r2_hidden('#skF_4'('#skF_6',k4_xboole_0('#skF_6','#skF_7')),k1_xboole_0)
    | r1_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1931,c_30])).

tff(c_1975,plain,(
    r1_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_1959])).

tff(c_24,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2065,plain,(
    ! [C_149] :
      ( ~ r2_hidden(C_149,k4_xboole_0('#skF_6','#skF_7'))
      | ~ r2_hidden(C_149,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1975,c_24])).

tff(c_2121,plain,(
    ! [D_150] :
      ( r2_hidden(D_150,'#skF_7')
      | ~ r2_hidden(D_150,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_2065])).

tff(c_221,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_213])).

tff(c_283,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_7','#skF_8')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_42])).

tff(c_307,plain,(
    k4_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_75])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_319,plain,(
    ! [D_8] :
      ( ~ r2_hidden(D_8,'#skF_8')
      | ~ r2_hidden(D_8,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_6])).

tff(c_2139,plain,(
    ! [D_151] :
      ( ~ r2_hidden(D_151,'#skF_8')
      | ~ r2_hidden(D_151,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2121,c_319])).

tff(c_2237,plain,(
    ! [B_159] :
      ( ~ r2_hidden('#skF_3'('#skF_6',B_159),'#skF_8')
      | r1_xboole_0('#skF_6',B_159) ) ),
    inference(resolution,[status(thm)],[c_28,c_2139])).

tff(c_2241,plain,(
    r1_xboole_0('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_2237])).

tff(c_2245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_2241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:10:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.62  
% 3.65/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 3.65/1.62  
% 3.65/1.62  %Foreground sorts:
% 3.65/1.62  
% 3.65/1.62  
% 3.65/1.62  %Background operators:
% 3.65/1.62  
% 3.65/1.62  
% 3.65/1.62  %Foreground operators:
% 3.65/1.62  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.65/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.65/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.65/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.65/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.65/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.65/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.65/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.65/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.65/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.65/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.65/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.65/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.65/1.62  
% 3.65/1.64  tff(f_98, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.65/1.64  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.65/1.64  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.65/1.64  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.65/1.64  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.65/1.64  tff(f_73, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.65/1.64  tff(f_91, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.65/1.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.65/1.64  tff(f_83, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.65/1.64  tff(f_89, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.65/1.64  tff(f_87, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.65/1.64  tff(c_44, plain, (~r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.65/1.64  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.65/1.64  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.65/1.64  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.65/1.64  tff(c_46, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.65/1.64  tff(c_145, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.64  tff(c_148, plain, (r1_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_46, c_145])).
% 3.65/1.64  tff(c_34, plain, (![A_21]: (r2_hidden('#skF_5'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.65/1.64  tff(c_198, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.65/1.64  tff(c_213, plain, (![A_48, B_49]: (~r1_xboole_0(A_48, B_49) | k3_xboole_0(A_48, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_198])).
% 3.65/1.64  tff(c_220, plain, (k3_xboole_0('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_148, c_213])).
% 3.65/1.64  tff(c_32, plain, (![A_16, B_17, C_20]: (~r1_xboole_0(A_16, B_17) | ~r2_hidden(C_20, k3_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.65/1.64  tff(c_225, plain, (![C_20]: (~r1_xboole_0('#skF_8', '#skF_7') | ~r2_hidden(C_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_220, c_32])).
% 3.65/1.64  tff(c_232, plain, (![C_20]: (~r2_hidden(C_20, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_225])).
% 3.65/1.64  tff(c_234, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_225])).
% 3.65/1.64  tff(c_246, plain, (![B_51]: (r1_xboole_0(k1_xboole_0, B_51))), inference(resolution, [status(thm)], [c_28, c_234])).
% 3.65/1.64  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.64  tff(c_268, plain, (![B_55]: (r1_xboole_0(B_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_246, c_22])).
% 3.65/1.64  tff(c_211, plain, (![A_45, B_46]: (~r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_198])).
% 3.65/1.64  tff(c_274, plain, (![B_55]: (k3_xboole_0(B_55, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_268, c_211])).
% 3.65/1.64  tff(c_345, plain, (![B_57]: (k3_xboole_0(B_57, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_268, c_211])).
% 3.65/1.64  tff(c_42, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.65/1.64  tff(c_700, plain, (![B_72]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_72, k1_xboole_0))=B_72)), inference(superposition, [status(thm), theory('equality')], [c_345, c_42])).
% 3.65/1.64  tff(c_59, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.65/1.64  tff(c_36, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.65/1.64  tff(c_75, plain, (![A_33]: (k2_xboole_0(k1_xboole_0, A_33)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_59, c_36])).
% 3.65/1.64  tff(c_732, plain, (![B_73]: (k4_xboole_0(B_73, k1_xboole_0)=B_73)), inference(superposition, [status(thm), theory('equality')], [c_700, c_75])).
% 3.65/1.64  tff(c_40, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.65/1.64  tff(c_751, plain, (![B_73]: (k4_xboole_0(B_73, B_73)=k3_xboole_0(B_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_732, c_40])).
% 3.65/1.64  tff(c_762, plain, (![B_73]: (k4_xboole_0(B_73, B_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_274, c_751])).
% 3.65/1.64  tff(c_48, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.65/1.64  tff(c_154, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.65/1.64  tff(c_158, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_48, c_154])).
% 3.65/1.64  tff(c_163, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.65/1.64  tff(c_1844, plain, (![A_143, B_144]: (k4_xboole_0(A_143, k3_xboole_0(A_143, B_144))=k3_xboole_0(A_143, k4_xboole_0(A_143, B_144)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_40])).
% 3.65/1.64  tff(c_1918, plain, (k3_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))=k4_xboole_0('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_158, c_1844])).
% 3.65/1.64  tff(c_1931, plain, (k3_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_762, c_1918])).
% 3.65/1.64  tff(c_30, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), k3_xboole_0(A_16, B_17)) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.65/1.64  tff(c_1959, plain, (r2_hidden('#skF_4'('#skF_6', k4_xboole_0('#skF_6', '#skF_7')), k1_xboole_0) | r1_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1931, c_30])).
% 3.65/1.64  tff(c_1975, plain, (r1_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_232, c_1959])).
% 3.65/1.64  tff(c_24, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, B_12) | ~r2_hidden(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.65/1.64  tff(c_2065, plain, (![C_149]: (~r2_hidden(C_149, k4_xboole_0('#skF_6', '#skF_7')) | ~r2_hidden(C_149, '#skF_6'))), inference(resolution, [status(thm)], [c_1975, c_24])).
% 3.65/1.64  tff(c_2121, plain, (![D_150]: (r2_hidden(D_150, '#skF_7') | ~r2_hidden(D_150, '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_2065])).
% 3.65/1.64  tff(c_221, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_213])).
% 3.65/1.64  tff(c_283, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_7', '#skF_8'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_221, c_42])).
% 3.65/1.64  tff(c_307, plain, (k4_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_283, c_75])).
% 3.65/1.64  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.65/1.64  tff(c_319, plain, (![D_8]: (~r2_hidden(D_8, '#skF_8') | ~r2_hidden(D_8, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_6])).
% 3.65/1.64  tff(c_2139, plain, (![D_151]: (~r2_hidden(D_151, '#skF_8') | ~r2_hidden(D_151, '#skF_6'))), inference(resolution, [status(thm)], [c_2121, c_319])).
% 3.65/1.64  tff(c_2237, plain, (![B_159]: (~r2_hidden('#skF_3'('#skF_6', B_159), '#skF_8') | r1_xboole_0('#skF_6', B_159))), inference(resolution, [status(thm)], [c_28, c_2139])).
% 3.65/1.64  tff(c_2241, plain, (r1_xboole_0('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_26, c_2237])).
% 3.65/1.64  tff(c_2245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_2241])).
% 3.65/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.64  
% 3.65/1.64  Inference rules
% 3.65/1.64  ----------------------
% 3.65/1.64  #Ref     : 0
% 3.65/1.64  #Sup     : 522
% 3.65/1.64  #Fact    : 0
% 3.65/1.64  #Define  : 0
% 3.65/1.64  #Split   : 8
% 3.65/1.64  #Chain   : 0
% 3.65/1.64  #Close   : 0
% 3.65/1.64  
% 3.65/1.64  Ordering : KBO
% 3.65/1.64  
% 3.65/1.64  Simplification rules
% 3.65/1.64  ----------------------
% 3.65/1.64  #Subsume      : 100
% 3.65/1.64  #Demod        : 263
% 3.65/1.64  #Tautology    : 262
% 3.65/1.64  #SimpNegUnit  : 19
% 3.65/1.64  #BackRed      : 6
% 3.65/1.64  
% 3.65/1.64  #Partial instantiations: 0
% 3.65/1.64  #Strategies tried      : 1
% 3.65/1.64  
% 3.65/1.64  Timing (in seconds)
% 3.65/1.64  ----------------------
% 3.65/1.64  Preprocessing        : 0.29
% 3.65/1.64  Parsing              : 0.16
% 3.65/1.64  CNF conversion       : 0.02
% 3.65/1.64  Main loop            : 0.58
% 3.65/1.64  Inferencing          : 0.20
% 3.65/1.64  Reduction            : 0.20
% 3.65/1.64  Demodulation         : 0.15
% 3.65/1.64  BG Simplification    : 0.02
% 3.65/1.64  Subsumption          : 0.10
% 3.65/1.64  Abstraction          : 0.02
% 3.65/1.64  MUC search           : 0.00
% 3.65/1.64  Cooper               : 0.00
% 3.65/1.64  Total                : 0.91
% 3.65/1.64  Index Insertion      : 0.00
% 3.65/1.64  Index Deletion       : 0.00
% 3.65/1.64  Index Matching       : 0.00
% 3.65/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
