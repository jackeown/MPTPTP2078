%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:03 EST 2020

% Result     : Theorem 8.22s
% Output     : CNFRefutation 8.39s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 199 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 269 expanded)
%              Number of equality atoms :   42 ( 117 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
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

tff(c_42,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_125,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | ~ r1_xboole_0(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_125])).

tff(c_142,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = A_48
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_149,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_128,c_142])).

tff(c_627,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k4_xboole_0(A_95,B_96),C_97) = k4_xboole_0(A_95,k2_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_697,plain,(
    ! [C_97] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_97)) = k4_xboole_0('#skF_3',C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_627])).

tff(c_257,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(A_56,B_57)
      | k4_xboole_0(A_56,B_57) != A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_269,plain,(
    ! [B_58,A_59] :
      ( r1_xboole_0(B_58,A_59)
      | k4_xboole_0(A_59,B_58) != A_59 ) ),
    inference(resolution,[status(thm)],[c_257,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_280,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_2')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_269,c_48])).

tff(c_1860,plain,(
    k4_xboole_0('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_280])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_206,plain,(
    ! [A_52,B_53] : k2_xboole_0(k4_xboole_0(A_52,B_53),A_52) = A_52 ),
    inference(resolution,[status(thm)],[c_16,c_165])).

tff(c_212,plain,(
    ! [A_52,B_53] : k2_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_338,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_356,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,k4_xboole_0(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_338])).

tff(c_1051,plain,(
    ! [A_110,B_111] : k3_xboole_0(A_110,k4_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_356])).

tff(c_1121,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_1051])).

tff(c_1143,plain,(
    k3_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1121])).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,k1_tarski(B_36)) = A_35
      | r2_hidden(B_36,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12276,plain,(
    ! [A_292,B_293] :
      ( k4_xboole_0(A_292,k1_tarski(B_293)) = k3_xboole_0(A_292,A_292)
      | r2_hidden(B_293,A_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1051])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_176,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_47,c_165])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k4_xboole_0(A_16,B_17),C_18) = k4_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_690,plain,(
    ! [A_19,B_20,C_97] : k4_xboole_0(A_19,k2_xboole_0(k3_xboole_0(A_19,B_20),C_97)) = k4_xboole_0(k4_xboole_0(A_19,B_20),C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_627])).

tff(c_2944,plain,(
    ! [A_151,B_152,C_153] : k4_xboole_0(A_151,k2_xboole_0(k3_xboole_0(A_151,B_152),C_153)) = k4_xboole_0(A_151,k2_xboole_0(B_152,C_153)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_690])).

tff(c_3056,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_2',k1_tarski('#skF_5'))) = k4_xboole_0('#skF_3',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_2944])).

tff(c_661,plain,(
    ! [A_95,B_96,C_97] : r1_tarski(k4_xboole_0(A_95,k2_xboole_0(B_96,C_97)),k4_xboole_0(A_95,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_16])).

tff(c_5781,plain,(
    r1_tarski(k4_xboole_0('#skF_3',k1_tarski('#skF_5')),k4_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3056,c_661])).

tff(c_12330,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_3'),k4_xboole_0('#skF_3','#skF_2'))
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12276,c_5781])).

tff(c_12569,plain,
    ( r1_tarski('#skF_3',k4_xboole_0('#skF_3','#skF_2'))
    | r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_12330])).

tff(c_14621,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12569])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_524,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,B_85)
      | ~ r2_hidden(C_86,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2433,plain,(
    ! [C_135,B_136,A_137] :
      ( ~ r2_hidden(C_135,B_136)
      | ~ r2_hidden(C_135,A_137)
      | k4_xboole_0(A_137,B_136) != A_137 ) ),
    inference(resolution,[status(thm)],[c_26,c_524])).

tff(c_2448,plain,(
    ! [A_137] :
      ( ~ r2_hidden('#skF_5',A_137)
      | k4_xboole_0(A_137,'#skF_4') != A_137 ) ),
    inference(resolution,[status(thm)],[c_44,c_2433])).

tff(c_14624,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_14621,c_2448])).

tff(c_14633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_14624])).

tff(c_14634,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12569])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14649,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_14634,c_14])).

tff(c_14651,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_14649])).

tff(c_14653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1860,c_14651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.22/3.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/3.33  
% 8.39/3.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/3.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.39/3.33  
% 8.39/3.33  %Foreground sorts:
% 8.39/3.33  
% 8.39/3.33  
% 8.39/3.33  %Background operators:
% 8.39/3.33  
% 8.39/3.33  
% 8.39/3.33  %Foreground operators:
% 8.39/3.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.39/3.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.39/3.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.39/3.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.39/3.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.39/3.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.39/3.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.39/3.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.39/3.33  tff('#skF_5', type, '#skF_5': $i).
% 8.39/3.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.39/3.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.39/3.33  tff('#skF_2', type, '#skF_2': $i).
% 8.39/3.33  tff('#skF_3', type, '#skF_3': $i).
% 8.39/3.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.39/3.33  tff('#skF_4', type, '#skF_4': $i).
% 8.39/3.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.39/3.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.39/3.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.39/3.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.39/3.33  
% 8.39/3.35  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.39/3.35  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.39/3.35  tff(f_67, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.39/3.35  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.39/3.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.39/3.35  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.39/3.35  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.39/3.35  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.39/3.35  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.39/3.35  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 8.39/3.35  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.39/3.35  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.39/3.35  tff(c_42, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.39/3.35  tff(c_125, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | ~r1_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.39/3.35  tff(c_128, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_125])).
% 8.39/3.35  tff(c_142, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=A_48 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.39/3.35  tff(c_149, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_128, c_142])).
% 8.39/3.35  tff(c_627, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k4_xboole_0(A_95, B_96), C_97)=k4_xboole_0(A_95, k2_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.39/3.35  tff(c_697, plain, (![C_97]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_97))=k4_xboole_0('#skF_3', C_97))), inference(superposition, [status(thm), theory('equality')], [c_149, c_627])).
% 8.39/3.35  tff(c_257, plain, (![A_56, B_57]: (r1_xboole_0(A_56, B_57) | k4_xboole_0(A_56, B_57)!=A_56)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.39/3.35  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.39/3.35  tff(c_269, plain, (![B_58, A_59]: (r1_xboole_0(B_58, A_59) | k4_xboole_0(A_59, B_58)!=A_59)), inference(resolution, [status(thm)], [c_257, c_6])).
% 8.39/3.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.39/3.35  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.39/3.35  tff(c_48, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 8.39/3.35  tff(c_280, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_2'))!='#skF_3'), inference(resolution, [status(thm)], [c_269, c_48])).
% 8.39/3.35  tff(c_1860, plain, (k4_xboole_0('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_697, c_280])).
% 8.39/3.35  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.39/3.35  tff(c_165, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.39/3.35  tff(c_206, plain, (![A_52, B_53]: (k2_xboole_0(k4_xboole_0(A_52, B_53), A_52)=A_52)), inference(resolution, [status(thm)], [c_16, c_165])).
% 8.39/3.35  tff(c_212, plain, (![A_52, B_53]: (k2_xboole_0(A_52, k4_xboole_0(A_52, B_53))=A_52)), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 8.39/3.35  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.39/3.35  tff(c_22, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.39/3.35  tff(c_338, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.39/3.35  tff(c_356, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k3_xboole_0(A_21, k4_xboole_0(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_338])).
% 8.39/3.35  tff(c_1051, plain, (![A_110, B_111]: (k3_xboole_0(A_110, k4_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_356])).
% 8.39/3.35  tff(c_1121, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_149, c_1051])).
% 8.39/3.35  tff(c_1143, plain, (k3_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1121])).
% 8.39/3.35  tff(c_38, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k1_tarski(B_36))=A_35 | r2_hidden(B_36, A_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.39/3.35  tff(c_12276, plain, (![A_292, B_293]: (k4_xboole_0(A_292, k1_tarski(B_293))=k3_xboole_0(A_292, A_292) | r2_hidden(B_293, A_292))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1051])).
% 8.39/3.35  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.39/3.35  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.39/3.35  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_46])).
% 8.39/3.35  tff(c_176, plain, (k2_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_47, c_165])).
% 8.39/3.35  tff(c_18, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k4_xboole_0(A_16, B_17), C_18)=k4_xboole_0(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.39/3.35  tff(c_690, plain, (![A_19, B_20, C_97]: (k4_xboole_0(A_19, k2_xboole_0(k3_xboole_0(A_19, B_20), C_97))=k4_xboole_0(k4_xboole_0(A_19, B_20), C_97))), inference(superposition, [status(thm), theory('equality')], [c_20, c_627])).
% 8.39/3.35  tff(c_2944, plain, (![A_151, B_152, C_153]: (k4_xboole_0(A_151, k2_xboole_0(k3_xboole_0(A_151, B_152), C_153))=k4_xboole_0(A_151, k2_xboole_0(B_152, C_153)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_690])).
% 8.39/3.35  tff(c_3056, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_2', k1_tarski('#skF_5')))=k4_xboole_0('#skF_3', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_2944])).
% 8.39/3.35  tff(c_661, plain, (![A_95, B_96, C_97]: (r1_tarski(k4_xboole_0(A_95, k2_xboole_0(B_96, C_97)), k4_xboole_0(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_627, c_16])).
% 8.39/3.35  tff(c_5781, plain, (r1_tarski(k4_xboole_0('#skF_3', k1_tarski('#skF_5')), k4_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3056, c_661])).
% 8.39/3.35  tff(c_12330, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_3'), k4_xboole_0('#skF_3', '#skF_2')) | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12276, c_5781])).
% 8.39/3.35  tff(c_12569, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_3', '#skF_2')) | r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_12330])).
% 8.39/3.35  tff(c_14621, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_12569])).
% 8.39/3.35  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.39/3.35  tff(c_26, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k4_xboole_0(A_23, B_24)!=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.39/3.35  tff(c_524, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, B_85) | ~r2_hidden(C_86, A_84))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.39/3.35  tff(c_2433, plain, (![C_135, B_136, A_137]: (~r2_hidden(C_135, B_136) | ~r2_hidden(C_135, A_137) | k4_xboole_0(A_137, B_136)!=A_137)), inference(resolution, [status(thm)], [c_26, c_524])).
% 8.39/3.35  tff(c_2448, plain, (![A_137]: (~r2_hidden('#skF_5', A_137) | k4_xboole_0(A_137, '#skF_4')!=A_137)), inference(resolution, [status(thm)], [c_44, c_2433])).
% 8.39/3.35  tff(c_14624, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(resolution, [status(thm)], [c_14621, c_2448])).
% 8.39/3.35  tff(c_14633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_14624])).
% 8.39/3.35  tff(c_14634, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_12569])).
% 8.39/3.35  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.39/3.35  tff(c_14649, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_14634, c_14])).
% 8.39/3.35  tff(c_14651, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_14649])).
% 8.39/3.35  tff(c_14653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1860, c_14651])).
% 8.39/3.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/3.35  
% 8.39/3.35  Inference rules
% 8.39/3.35  ----------------------
% 8.39/3.35  #Ref     : 0
% 8.39/3.35  #Sup     : 3565
% 8.39/3.35  #Fact    : 0
% 8.39/3.35  #Define  : 0
% 8.39/3.35  #Split   : 1
% 8.39/3.35  #Chain   : 0
% 8.39/3.35  #Close   : 0
% 8.39/3.35  
% 8.39/3.35  Ordering : KBO
% 8.39/3.35  
% 8.39/3.35  Simplification rules
% 8.39/3.35  ----------------------
% 8.39/3.35  #Subsume      : 47
% 8.39/3.35  #Demod        : 3195
% 8.39/3.35  #Tautology    : 2071
% 8.39/3.35  #SimpNegUnit  : 1
% 8.39/3.35  #BackRed      : 11
% 8.39/3.35  
% 8.39/3.35  #Partial instantiations: 0
% 8.39/3.35  #Strategies tried      : 1
% 8.39/3.35  
% 8.39/3.35  Timing (in seconds)
% 8.39/3.35  ----------------------
% 8.39/3.35  Preprocessing        : 0.31
% 8.39/3.35  Parsing              : 0.17
% 8.39/3.35  CNF conversion       : 0.02
% 8.39/3.35  Main loop            : 2.27
% 8.39/3.35  Inferencing          : 0.51
% 8.39/3.35  Reduction            : 1.22
% 8.39/3.35  Demodulation         : 1.06
% 8.39/3.35  BG Simplification    : 0.07
% 8.39/3.35  Subsumption          : 0.36
% 8.39/3.35  Abstraction          : 0.09
% 8.39/3.35  MUC search           : 0.00
% 8.39/3.35  Cooper               : 0.00
% 8.39/3.35  Total                : 2.62
% 8.39/3.35  Index Insertion      : 0.00
% 8.39/3.35  Index Deletion       : 0.00
% 8.39/3.35  Index Matching       : 0.00
% 8.39/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
