%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:27 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 150 expanded)
%              Number of leaves         :   40 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 217 expanded)
%              Number of equality atoms :   56 ( 134 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_65,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_90,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_5'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_449,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_464,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = k4_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_449])).

tff(c_469,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_464])).

tff(c_44,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_215,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(A_67,B_68) = B_68
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_233,plain,(
    ! [B_69] : k2_xboole_0(B_69,B_69) = B_69 ),
    inference(resolution,[status(thm)],[c_44,c_215])).

tff(c_52,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_239,plain,(
    ! [B_69] : k4_xboole_0(B_69,B_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_52])).

tff(c_308,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_323,plain,(
    ! [B_69] : k4_xboole_0(B_69,k1_xboole_0) = k3_xboole_0(B_69,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_308])).

tff(c_471,plain,(
    ! [B_69] : k3_xboole_0(B_69,B_69) = B_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_323])).

tff(c_92,plain,(
    k2_xboole_0('#skF_9','#skF_10') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_141,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k2_xboole_0(A_58,B_59)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_148,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_141])).

tff(c_326,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k4_xboole_0('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_308])).

tff(c_423,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k3_xboole_0('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_326])).

tff(c_508,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_423])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_572,plain,(
    ! [D_97] :
      ( r2_hidden(D_97,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_97,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_22])).

tff(c_60,plain,(
    ! [C_33,A_29] :
      ( C_33 = A_29
      | ~ r2_hidden(C_33,k1_tarski(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_587,plain,(
    ! [D_101] :
      ( D_101 = '#skF_8'
      | ~ r2_hidden(D_101,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_572,c_60])).

tff(c_591,plain,
    ( '#skF_5'('#skF_9') = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_587])).

tff(c_594,plain,(
    '#skF_5'('#skF_9') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_591])).

tff(c_598,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_38])).

tff(c_601,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_598])).

tff(c_82,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tarski(A_44),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_125,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_58])).

tff(c_644,plain,(
    ! [B_107,A_108] :
      ( B_107 = A_108
      | ~ r1_tarski(B_107,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_654,plain,
    ( k1_tarski('#skF_8') = '#skF_9'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_125,c_644])).

tff(c_669,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_672,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_669])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_672])).

tff(c_677,plain,(
    k1_tarski('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_685,plain,(
    k2_xboole_0('#skF_9','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_92])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_577,plain,(
    ! [D_98,B_99,A_100] :
      ( ~ r2_hidden(D_98,B_99)
      | r2_hidden(D_98,k2_xboole_0(A_100,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_608,plain,(
    ! [D_102] :
      ( ~ r2_hidden(D_102,'#skF_10')
      | r2_hidden(D_102,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_577])).

tff(c_613,plain,(
    ! [D_103] :
      ( D_103 = '#skF_8'
      | ~ r2_hidden(D_103,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_608,c_60])).

tff(c_617,plain,
    ( '#skF_5'('#skF_10') = '#skF_8'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_38,c_613])).

tff(c_620,plain,(
    '#skF_5'('#skF_10') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_617])).

tff(c_624,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_38])).

tff(c_627,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_624])).

tff(c_812,plain,(
    ! [B_119] :
      ( r1_tarski('#skF_9',B_119)
      | ~ r2_hidden('#skF_8',B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_82])).

tff(c_845,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_627,c_812])).

tff(c_48,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_857,plain,(
    k2_xboole_0('#skF_9','#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_845,c_48])).

tff(c_862,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_857])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.53  
% 3.08/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.53  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7
% 3.08/1.53  
% 3.08/1.53  %Foreground sorts:
% 3.08/1.53  
% 3.08/1.53  
% 3.08/1.53  %Background operators:
% 3.08/1.53  
% 3.08/1.53  
% 3.08/1.53  %Foreground operators:
% 3.08/1.53  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.08/1.53  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.08/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.08/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.08/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.08/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.08/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.08/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.08/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.08/1.53  tff('#skF_10', type, '#skF_10': $i).
% 3.08/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.08/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.08/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.08/1.53  tff('#skF_9', type, '#skF_9': $i).
% 3.08/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.08/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.08/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.08/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.08/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.08/1.53  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.08/1.53  
% 3.08/1.55  tff(f_107, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.08/1.55  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.08/1.55  tff(f_71, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.08/1.55  tff(f_65, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.08/1.55  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.08/1.55  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.55  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.08/1.55  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.08/1.55  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.08/1.55  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.08/1.55  tff(f_80, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.08/1.55  tff(f_92, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.08/1.55  tff(f_73, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.08/1.55  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.08/1.55  tff(c_90, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.08/1.55  tff(c_88, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.08/1.55  tff(c_38, plain, (![A_13]: (r2_hidden('#skF_5'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.55  tff(c_56, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.08/1.55  tff(c_50, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.55  tff(c_449, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.55  tff(c_464, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=k4_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_449])).
% 3.08/1.55  tff(c_469, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_464])).
% 3.08/1.55  tff(c_44, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.55  tff(c_215, plain, (![A_67, B_68]: (k2_xboole_0(A_67, B_68)=B_68 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.08/1.55  tff(c_233, plain, (![B_69]: (k2_xboole_0(B_69, B_69)=B_69)), inference(resolution, [status(thm)], [c_44, c_215])).
% 3.08/1.55  tff(c_52, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.55  tff(c_239, plain, (![B_69]: (k4_xboole_0(B_69, B_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_233, c_52])).
% 3.08/1.55  tff(c_308, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.08/1.55  tff(c_323, plain, (![B_69]: (k4_xboole_0(B_69, k1_xboole_0)=k3_xboole_0(B_69, B_69))), inference(superposition, [status(thm), theory('equality')], [c_239, c_308])).
% 3.08/1.55  tff(c_471, plain, (![B_69]: (k3_xboole_0(B_69, B_69)=B_69)), inference(demodulation, [status(thm), theory('equality')], [c_469, c_323])).
% 3.08/1.55  tff(c_92, plain, (k2_xboole_0('#skF_9', '#skF_10')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.08/1.55  tff(c_141, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k2_xboole_0(A_58, B_59))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.55  tff(c_148, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92, c_141])).
% 3.08/1.55  tff(c_326, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k4_xboole_0('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_308])).
% 3.08/1.55  tff(c_423, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k3_xboole_0('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_326])).
% 3.08/1.55  tff(c_508, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_471, c_423])).
% 3.08/1.55  tff(c_22, plain, (![D_12, B_8, A_7]: (r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k3_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.55  tff(c_572, plain, (![D_97]: (r2_hidden(D_97, k1_tarski('#skF_8')) | ~r2_hidden(D_97, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_508, c_22])).
% 3.08/1.55  tff(c_60, plain, (![C_33, A_29]: (C_33=A_29 | ~r2_hidden(C_33, k1_tarski(A_29)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.08/1.55  tff(c_587, plain, (![D_101]: (D_101='#skF_8' | ~r2_hidden(D_101, '#skF_9'))), inference(resolution, [status(thm)], [c_572, c_60])).
% 3.08/1.55  tff(c_591, plain, ('#skF_5'('#skF_9')='#skF_8' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_38, c_587])).
% 3.08/1.55  tff(c_594, plain, ('#skF_5'('#skF_9')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_88, c_591])).
% 3.08/1.55  tff(c_598, plain, (r2_hidden('#skF_8', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_594, c_38])).
% 3.08/1.55  tff(c_601, plain, (r2_hidden('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_88, c_598])).
% 3.08/1.55  tff(c_82, plain, (![A_44, B_45]: (r1_tarski(k1_tarski(A_44), B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.08/1.55  tff(c_58, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.08/1.55  tff(c_125, plain, (r1_tarski('#skF_9', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_58])).
% 3.08/1.55  tff(c_644, plain, (![B_107, A_108]: (B_107=A_108 | ~r1_tarski(B_107, A_108) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.55  tff(c_654, plain, (k1_tarski('#skF_8')='#skF_9' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_125, c_644])).
% 3.08/1.55  tff(c_669, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_654])).
% 3.08/1.55  tff(c_672, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_82, c_669])).
% 3.08/1.55  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_601, c_672])).
% 3.08/1.55  tff(c_677, plain, (k1_tarski('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_654])).
% 3.08/1.55  tff(c_685, plain, (k2_xboole_0('#skF_9', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_677, c_92])).
% 3.08/1.55  tff(c_86, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.08/1.55  tff(c_577, plain, (![D_98, B_99, A_100]: (~r2_hidden(D_98, B_99) | r2_hidden(D_98, k2_xboole_0(A_100, B_99)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.55  tff(c_608, plain, (![D_102]: (~r2_hidden(D_102, '#skF_10') | r2_hidden(D_102, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_577])).
% 3.08/1.55  tff(c_613, plain, (![D_103]: (D_103='#skF_8' | ~r2_hidden(D_103, '#skF_10'))), inference(resolution, [status(thm)], [c_608, c_60])).
% 3.08/1.55  tff(c_617, plain, ('#skF_5'('#skF_10')='#skF_8' | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_38, c_613])).
% 3.08/1.55  tff(c_620, plain, ('#skF_5'('#skF_10')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_86, c_617])).
% 3.08/1.55  tff(c_624, plain, (r2_hidden('#skF_8', '#skF_10') | k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_620, c_38])).
% 3.08/1.55  tff(c_627, plain, (r2_hidden('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_86, c_624])).
% 3.08/1.55  tff(c_812, plain, (![B_119]: (r1_tarski('#skF_9', B_119) | ~r2_hidden('#skF_8', B_119))), inference(superposition, [status(thm), theory('equality')], [c_677, c_82])).
% 3.08/1.55  tff(c_845, plain, (r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_627, c_812])).
% 3.08/1.55  tff(c_48, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.08/1.55  tff(c_857, plain, (k2_xboole_0('#skF_9', '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_845, c_48])).
% 3.08/1.55  tff(c_862, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_685, c_857])).
% 3.08/1.55  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_862])).
% 3.08/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.55  
% 3.08/1.55  Inference rules
% 3.08/1.55  ----------------------
% 3.08/1.55  #Ref     : 0
% 3.08/1.55  #Sup     : 182
% 3.08/1.55  #Fact    : 0
% 3.08/1.55  #Define  : 0
% 3.08/1.55  #Split   : 1
% 3.08/1.55  #Chain   : 0
% 3.08/1.55  #Close   : 0
% 3.08/1.55  
% 3.08/1.55  Ordering : KBO
% 3.08/1.55  
% 3.08/1.55  Simplification rules
% 3.08/1.55  ----------------------
% 3.08/1.55  #Subsume      : 5
% 3.08/1.55  #Demod        : 76
% 3.08/1.55  #Tautology    : 133
% 3.08/1.55  #SimpNegUnit  : 8
% 3.08/1.55  #BackRed      : 13
% 3.08/1.55  
% 3.08/1.55  #Partial instantiations: 0
% 3.08/1.55  #Strategies tried      : 1
% 3.08/1.55  
% 3.08/1.55  Timing (in seconds)
% 3.08/1.55  ----------------------
% 3.08/1.55  Preprocessing        : 0.36
% 3.08/1.55  Parsing              : 0.18
% 3.08/1.55  CNF conversion       : 0.03
% 3.08/1.55  Main loop            : 0.31
% 3.08/1.55  Inferencing          : 0.10
% 3.08/1.55  Reduction            : 0.11
% 3.08/1.55  Demodulation         : 0.08
% 3.08/1.55  BG Simplification    : 0.02
% 3.08/1.55  Subsumption          : 0.06
% 3.08/1.55  Abstraction          : 0.01
% 3.08/1.55  MUC search           : 0.00
% 3.08/1.55  Cooper               : 0.00
% 3.08/1.55  Total                : 0.71
% 3.08/1.55  Index Insertion      : 0.00
% 3.08/1.55  Index Deletion       : 0.00
% 3.08/1.55  Index Matching       : 0.00
% 3.08/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
