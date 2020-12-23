%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:11 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :   70 (  96 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 165 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_649,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,B_118)
      | ~ r2_hidden(C_119,A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_704,plain,(
    ! [C_120] :
      ( ~ r2_hidden(C_120,'#skF_4')
      | ~ r2_hidden(C_120,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_649])).

tff(c_718,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_704])).

tff(c_111,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,B_47)
      | k4_xboole_0(A_46,B_47) != A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [B_47,A_46] :
      ( r1_xboole_0(B_47,A_46)
      | k4_xboole_0(A_46,B_47) != A_46 ) ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_62,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_62])).

tff(c_808,plain,(
    ! [A_130,C_131,B_132] :
      ( ~ r1_xboole_0(A_130,C_131)
      | ~ r1_xboole_0(A_130,B_132)
      | r1_xboole_0(A_130,k2_xboole_0(B_132,C_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2864,plain,(
    ! [B_257,C_258,A_259] :
      ( r1_xboole_0(k2_xboole_0(B_257,C_258),A_259)
      | ~ r1_xboole_0(A_259,C_258)
      | ~ r1_xboole_0(A_259,B_257) ) ),
    inference(resolution,[status(thm)],[c_808,c_4])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2912,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2864,c_44])).

tff(c_2929,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2912])).

tff(c_2936,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_117,c_2929])).

tff(c_280,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,k1_tarski(B_65)) = A_64
      | r2_hidden(B_65,A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_292,plain,(
    ! [A_64,B_65] :
      ( r1_xboole_0(A_64,k1_tarski(B_65))
      | r2_hidden(B_65,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_51,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_458,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95,B_96),B_96)
      | r1_xboole_0(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_463,plain,(
    ! [A_10,B_11,A_95] :
      ( ~ r1_xboole_0(A_10,B_11)
      | r1_xboole_0(A_95,k3_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_458,c_14])).

tff(c_923,plain,(
    ! [A_144,B_145,C_146] :
      ( ~ r1_xboole_0(A_144,k3_xboole_0(B_145,C_146))
      | ~ r1_tarski(A_144,C_146)
      | r1_xboole_0(A_144,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1863,plain,(
    ! [A_209,B_210,A_211] :
      ( ~ r1_tarski(A_209,B_210)
      | r1_xboole_0(A_209,A_211)
      | ~ r1_xboole_0(A_211,B_210) ) ),
    inference(resolution,[status(thm)],[c_463,c_923])).

tff(c_2133,plain,(
    ! [A_231] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_231)
      | ~ r1_xboole_0(A_231,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_51,c_1863])).

tff(c_2289,plain,(
    ! [A_235] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_235)
      | r2_hidden('#skF_6',A_235) ) ),
    inference(resolution,[status(thm)],[c_292,c_2133])).

tff(c_470,plain,(
    ! [A_99,B_100,A_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | r1_xboole_0(A_101,k3_xboole_0(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_458,c_14])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1376,plain,(
    ! [A_188,A_189,B_190] :
      ( k4_xboole_0(A_188,k3_xboole_0(A_189,B_190)) = A_188
      | ~ r1_xboole_0(A_189,B_190) ) ),
    inference(resolution,[status(thm)],[c_470,c_28])).

tff(c_119,plain,(
    ! [A_48,B_49] : r1_xboole_0(k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)),B_49) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_246,plain,(
    ! [B_60,A_61] : r1_xboole_0(B_60,k4_xboole_0(A_61,k3_xboole_0(A_61,B_60))) ),
    inference(resolution,[status(thm)],[c_119,c_4])).

tff(c_258,plain,(
    ! [B_60,A_61] : k4_xboole_0(B_60,k4_xboole_0(A_61,k3_xboole_0(A_61,B_60))) = B_60 ),
    inference(resolution,[status(thm)],[c_246,c_28])).

tff(c_1412,plain,(
    ! [B_190,A_189] :
      ( k4_xboole_0(B_190,A_189) = B_190
      | ~ r1_xboole_0(A_189,B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_258])).

tff(c_4198,plain,(
    ! [A_330] :
      ( k4_xboole_0(A_330,k3_xboole_0('#skF_4','#skF_3')) = A_330
      | r2_hidden('#skF_6',A_330) ) ),
    inference(resolution,[status(thm)],[c_2289,c_1412])).

tff(c_4243,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | r2_hidden('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4198,c_258])).

tff(c_4310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_718,c_2936,c_4243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:22:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.93/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/1.99  
% 5.23/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.23/2.00  
% 5.23/2.00  %Foreground sorts:
% 5.23/2.00  
% 5.23/2.00  
% 5.23/2.00  %Background operators:
% 5.23/2.00  
% 5.23/2.00  
% 5.23/2.00  %Foreground operators:
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.23/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.23/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.23/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.23/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.23/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.23/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.23/2.00  tff('#skF_6', type, '#skF_6': $i).
% 5.23/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.23/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.23/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.23/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.23/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.23/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.23/2.00  
% 5.23/2.01  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.23/2.01  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.23/2.01  tff(f_95, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.23/2.01  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.23/2.01  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.23/2.01  tff(f_108, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.23/2.01  tff(f_91, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.23/2.01  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.23/2.01  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.23/2.01  tff(f_89, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 5.23/2.01  tff(f_97, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 5.23/2.01  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.23/2.01  tff(c_46, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.23/2.01  tff(c_649, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, B_118) | ~r2_hidden(C_119, A_117))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.23/2.01  tff(c_704, plain, (![C_120]: (~r2_hidden(C_120, '#skF_4') | ~r2_hidden(C_120, '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_649])).
% 5.23/2.01  tff(c_718, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_704])).
% 5.23/2.01  tff(c_111, plain, (![A_46, B_47]: (r1_xboole_0(A_46, B_47) | k4_xboole_0(A_46, B_47)!=A_46)), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.23/2.01  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.01  tff(c_117, plain, (![B_47, A_46]: (r1_xboole_0(B_47, A_46) | k4_xboole_0(A_46, B_47)!=A_46)), inference(resolution, [status(thm)], [c_111, c_4])).
% 5.23/2.01  tff(c_62, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.01  tff(c_68, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_62])).
% 5.23/2.01  tff(c_808, plain, (![A_130, C_131, B_132]: (~r1_xboole_0(A_130, C_131) | ~r1_xboole_0(A_130, B_132) | r1_xboole_0(A_130, k2_xboole_0(B_132, C_131)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.23/2.01  tff(c_2864, plain, (![B_257, C_258, A_259]: (r1_xboole_0(k2_xboole_0(B_257, C_258), A_259) | ~r1_xboole_0(A_259, C_258) | ~r1_xboole_0(A_259, B_257))), inference(resolution, [status(thm)], [c_808, c_4])).
% 5.23/2.01  tff(c_44, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.23/2.01  tff(c_2912, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2864, c_44])).
% 5.23/2.01  tff(c_2929, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2912])).
% 5.23/2.01  tff(c_2936, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(resolution, [status(thm)], [c_117, c_2929])).
% 5.23/2.01  tff(c_280, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k1_tarski(B_65))=A_64 | r2_hidden(B_65, A_64))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.23/2.01  tff(c_26, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.23/2.01  tff(c_292, plain, (![A_64, B_65]: (r1_xboole_0(A_64, k1_tarski(B_65)) | r2_hidden(B_65, A_64))), inference(superposition, [status(thm), theory('equality')], [c_280, c_26])).
% 5.23/2.01  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.23/2.01  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.23/2.01  tff(c_51, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 5.23/2.01  tff(c_458, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95, B_96), B_96) | r1_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.23/2.01  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.01  tff(c_463, plain, (![A_10, B_11, A_95]: (~r1_xboole_0(A_10, B_11) | r1_xboole_0(A_95, k3_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_458, c_14])).
% 5.23/2.01  tff(c_923, plain, (![A_144, B_145, C_146]: (~r1_xboole_0(A_144, k3_xboole_0(B_145, C_146)) | ~r1_tarski(A_144, C_146) | r1_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.23/2.01  tff(c_1863, plain, (![A_209, B_210, A_211]: (~r1_tarski(A_209, B_210) | r1_xboole_0(A_209, A_211) | ~r1_xboole_0(A_211, B_210))), inference(resolution, [status(thm)], [c_463, c_923])).
% 5.23/2.01  tff(c_2133, plain, (![A_231]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_231) | ~r1_xboole_0(A_231, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_51, c_1863])).
% 5.23/2.01  tff(c_2289, plain, (![A_235]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_235) | r2_hidden('#skF_6', A_235))), inference(resolution, [status(thm)], [c_292, c_2133])).
% 5.23/2.01  tff(c_470, plain, (![A_99, B_100, A_101]: (~r1_xboole_0(A_99, B_100) | r1_xboole_0(A_101, k3_xboole_0(A_99, B_100)))), inference(resolution, [status(thm)], [c_458, c_14])).
% 5.23/2.01  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.23/2.01  tff(c_1376, plain, (![A_188, A_189, B_190]: (k4_xboole_0(A_188, k3_xboole_0(A_189, B_190))=A_188 | ~r1_xboole_0(A_189, B_190))), inference(resolution, [status(thm)], [c_470, c_28])).
% 5.23/2.01  tff(c_119, plain, (![A_48, B_49]: (r1_xboole_0(k4_xboole_0(A_48, k3_xboole_0(A_48, B_49)), B_49))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.23/2.01  tff(c_246, plain, (![B_60, A_61]: (r1_xboole_0(B_60, k4_xboole_0(A_61, k3_xboole_0(A_61, B_60))))), inference(resolution, [status(thm)], [c_119, c_4])).
% 5.23/2.01  tff(c_258, plain, (![B_60, A_61]: (k4_xboole_0(B_60, k4_xboole_0(A_61, k3_xboole_0(A_61, B_60)))=B_60)), inference(resolution, [status(thm)], [c_246, c_28])).
% 5.23/2.01  tff(c_1412, plain, (![B_190, A_189]: (k4_xboole_0(B_190, A_189)=B_190 | ~r1_xboole_0(A_189, B_190))), inference(superposition, [status(thm), theory('equality')], [c_1376, c_258])).
% 5.23/2.01  tff(c_4198, plain, (![A_330]: (k4_xboole_0(A_330, k3_xboole_0('#skF_4', '#skF_3'))=A_330 | r2_hidden('#skF_6', A_330))), inference(resolution, [status(thm)], [c_2289, c_1412])).
% 5.23/2.01  tff(c_4243, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | r2_hidden('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4198, c_258])).
% 5.23/2.01  tff(c_4310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_718, c_2936, c_4243])).
% 5.23/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.01  
% 5.23/2.01  Inference rules
% 5.23/2.01  ----------------------
% 5.23/2.01  #Ref     : 0
% 5.23/2.01  #Sup     : 974
% 5.23/2.01  #Fact    : 0
% 5.23/2.01  #Define  : 0
% 5.23/2.01  #Split   : 0
% 5.23/2.01  #Chain   : 0
% 5.23/2.01  #Close   : 0
% 5.23/2.01  
% 5.23/2.01  Ordering : KBO
% 5.23/2.01  
% 5.23/2.01  Simplification rules
% 5.23/2.01  ----------------------
% 5.23/2.01  #Subsume      : 183
% 5.23/2.01  #Demod        : 171
% 5.23/2.01  #Tautology    : 268
% 5.23/2.01  #SimpNegUnit  : 6
% 5.23/2.01  #BackRed      : 0
% 5.23/2.01  
% 5.23/2.01  #Partial instantiations: 0
% 5.23/2.01  #Strategies tried      : 1
% 5.23/2.01  
% 5.23/2.01  Timing (in seconds)
% 5.23/2.01  ----------------------
% 5.23/2.02  Preprocessing        : 0.33
% 5.23/2.02  Parsing              : 0.17
% 5.23/2.02  CNF conversion       : 0.02
% 5.23/2.02  Main loop            : 0.94
% 5.23/2.02  Inferencing          : 0.32
% 5.23/2.02  Reduction            : 0.33
% 5.23/2.02  Demodulation         : 0.25
% 5.23/2.02  BG Simplification    : 0.04
% 5.23/2.02  Subsumption          : 0.19
% 5.23/2.02  Abstraction          : 0.04
% 5.23/2.02  MUC search           : 0.00
% 5.23/2.02  Cooper               : 0.00
% 5.23/2.02  Total                : 1.30
% 5.23/2.02  Index Insertion      : 0.00
% 5.23/2.02  Index Deletion       : 0.00
% 5.23/2.02  Index Matching       : 0.00
% 5.23/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
