%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:37 EST 2020

% Result     : Theorem 12.17s
% Output     : CNFRefutation 12.17s
% Verified   : 
% Statistics : Number of formulae       :   66 (  92 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 159 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_48,plain,(
    k1_relat_1(k7_relat_1('#skF_7','#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1428,plain,(
    ! [A_142,B_143,B_144] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_142,B_143),B_144),A_142)
      | r1_tarski(k4_xboole_0(A_142,B_143),B_144) ) ),
    inference(resolution,[status(thm)],[c_146,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1502,plain,(
    ! [A_142,B_143] : r1_tarski(k4_xboole_0(A_142,B_143),A_142) ),
    inference(resolution,[status(thm)],[c_1428,c_6])).

tff(c_50,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_227,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_844,plain,(
    ! [A_94,B_95,B_96] :
      ( r2_hidden('#skF_1'(A_94,B_95),B_96)
      | ~ r1_tarski(A_94,B_96)
      | r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_8,c_227])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34990,plain,(
    ! [A_734,B_735,B_736,B_737] :
      ( r2_hidden('#skF_1'(A_734,B_735),B_736)
      | ~ r1_tarski(B_737,B_736)
      | ~ r1_tarski(A_734,B_737)
      | r1_tarski(A_734,B_735) ) ),
    inference(resolution,[status(thm)],[c_844,c_4])).

tff(c_35066,plain,(
    ! [A_738,B_739] :
      ( r2_hidden('#skF_1'(A_738,B_739),k1_relat_1('#skF_7'))
      | ~ r1_tarski(A_738,'#skF_6')
      | r1_tarski(A_738,B_739) ) ),
    inference(resolution,[status(thm)],[c_50,c_34990])).

tff(c_35087,plain,(
    ! [A_740] :
      ( ~ r1_tarski(A_740,'#skF_6')
      | r1_tarski(A_740,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_35066,c_6])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),B_15)
      | r2_hidden('#skF_5'(A_14,B_15),A_14)
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_506,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_4'(A_79,B_80),B_80)
      | r2_hidden('#skF_5'(A_79,B_80),A_79)
      | B_80 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_130,plain,(
    ! [D_35,B_36,A_37] :
      ( ~ r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k4_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    ! [D_35,A_17] :
      ( ~ r2_hidden(D_35,k1_xboole_0)
      | ~ r2_hidden(D_35,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_130])).

tff(c_2028,plain,(
    ! [B_178,A_179] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,B_178),A_179)
      | r2_hidden('#skF_4'(k1_xboole_0,B_178),B_178)
      | k1_xboole_0 = B_178 ) ),
    inference(resolution,[status(thm)],[c_506,c_136])).

tff(c_2053,plain,(
    ! [B_180] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_180),B_180)
      | k1_xboole_0 = B_180 ) ),
    inference(resolution,[status(thm)],[c_34,c_2028])).

tff(c_2102,plain,(
    ! [B_180,B_4] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_180),B_4)
      | ~ r1_tarski(B_180,B_4)
      | k1_xboole_0 = B_180 ) ),
    inference(resolution,[status(thm)],[c_2053,c_4])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2392,plain,(
    ! [A_189,B_190] :
      ( ~ r2_hidden('#skF_4'(k1_xboole_0,k4_xboole_0(A_189,B_190)),B_190)
      | k4_xboole_0(A_189,B_190) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2053,c_12])).

tff(c_2437,plain,(
    ! [A_189,B_4] :
      ( ~ r1_tarski(k4_xboole_0(A_189,B_4),B_4)
      | k4_xboole_0(A_189,B_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2102,c_2392])).

tff(c_35104,plain,(
    ! [A_741] :
      ( k4_xboole_0(A_741,k1_relat_1('#skF_7')) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_741,k1_relat_1('#skF_7')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_35087,c_2437])).

tff(c_35132,plain,(
    k4_xboole_0('#skF_6',k1_relat_1('#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1502,c_35104])).

tff(c_38,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_35546,plain,(
    k3_xboole_0('#skF_6',k1_relat_1('#skF_7')) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_35132,c_38])).

tff(c_35662,plain,(
    k3_xboole_0('#skF_6',k1_relat_1('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_35546])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_303,plain,(
    ! [B_58,A_59] :
      ( k3_xboole_0(k1_relat_1(B_58),A_59) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_327,plain,(
    ! [B_2,B_58] :
      ( k3_xboole_0(B_2,k1_relat_1(B_58)) = k1_relat_1(k7_relat_1(B_58,B_2))
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_303])).

tff(c_35904,plain,
    ( k1_relat_1(k7_relat_1('#skF_7','#skF_6')) = '#skF_6'
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_35662,c_327])).

tff(c_35990,plain,(
    k1_relat_1(k7_relat_1('#skF_7','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_35904])).

tff(c_35992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_35990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.17/5.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.69  
% 12.17/5.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.69  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 12.17/5.69  
% 12.17/5.69  %Foreground sorts:
% 12.17/5.69  
% 12.17/5.69  
% 12.17/5.69  %Background operators:
% 12.17/5.69  
% 12.17/5.69  
% 12.17/5.69  %Foreground operators:
% 12.17/5.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.17/5.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.17/5.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.17/5.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.17/5.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.17/5.69  tff('#skF_7', type, '#skF_7': $i).
% 12.17/5.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.17/5.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.17/5.69  tff('#skF_6', type, '#skF_6': $i).
% 12.17/5.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.17/5.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.17/5.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.17/5.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.17/5.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.17/5.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.17/5.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.17/5.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.17/5.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.17/5.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.17/5.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.17/5.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.17/5.69  
% 12.17/5.71  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 12.17/5.71  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.17/5.71  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.17/5.71  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.17/5.71  tff(f_51, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 12.17/5.71  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.17/5.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.17/5.71  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 12.17/5.71  tff(c_48, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.17/5.71  tff(c_52, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.17/5.71  tff(c_36, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.17/5.71  tff(c_146, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.17/5.71  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.17/5.71  tff(c_1428, plain, (![A_142, B_143, B_144]: (r2_hidden('#skF_1'(k4_xboole_0(A_142, B_143), B_144), A_142) | r1_tarski(k4_xboole_0(A_142, B_143), B_144))), inference(resolution, [status(thm)], [c_146, c_14])).
% 12.17/5.71  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.17/5.71  tff(c_1502, plain, (![A_142, B_143]: (r1_tarski(k4_xboole_0(A_142, B_143), A_142))), inference(resolution, [status(thm)], [c_1428, c_6])).
% 12.17/5.71  tff(c_50, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.17/5.71  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.17/5.71  tff(c_227, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.17/5.71  tff(c_844, plain, (![A_94, B_95, B_96]: (r2_hidden('#skF_1'(A_94, B_95), B_96) | ~r1_tarski(A_94, B_96) | r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_8, c_227])).
% 12.17/5.71  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.17/5.71  tff(c_34990, plain, (![A_734, B_735, B_736, B_737]: (r2_hidden('#skF_1'(A_734, B_735), B_736) | ~r1_tarski(B_737, B_736) | ~r1_tarski(A_734, B_737) | r1_tarski(A_734, B_735))), inference(resolution, [status(thm)], [c_844, c_4])).
% 12.17/5.71  tff(c_35066, plain, (![A_738, B_739]: (r2_hidden('#skF_1'(A_738, B_739), k1_relat_1('#skF_7')) | ~r1_tarski(A_738, '#skF_6') | r1_tarski(A_738, B_739))), inference(resolution, [status(thm)], [c_50, c_34990])).
% 12.17/5.71  tff(c_35087, plain, (![A_740]: (~r1_tarski(A_740, '#skF_6') | r1_tarski(A_740, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_35066, c_6])).
% 12.17/5.71  tff(c_34, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), B_15) | r2_hidden('#skF_5'(A_14, B_15), A_14) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.17/5.71  tff(c_506, plain, (![A_79, B_80]: (r2_hidden('#skF_4'(A_79, B_80), B_80) | r2_hidden('#skF_5'(A_79, B_80), A_79) | B_80=A_79)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.17/5.71  tff(c_130, plain, (![D_35, B_36, A_37]: (~r2_hidden(D_35, B_36) | ~r2_hidden(D_35, k4_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.17/5.71  tff(c_136, plain, (![D_35, A_17]: (~r2_hidden(D_35, k1_xboole_0) | ~r2_hidden(D_35, A_17))), inference(superposition, [status(thm), theory('equality')], [c_36, c_130])).
% 12.17/5.71  tff(c_2028, plain, (![B_178, A_179]: (~r2_hidden('#skF_5'(k1_xboole_0, B_178), A_179) | r2_hidden('#skF_4'(k1_xboole_0, B_178), B_178) | k1_xboole_0=B_178)), inference(resolution, [status(thm)], [c_506, c_136])).
% 12.17/5.71  tff(c_2053, plain, (![B_180]: (r2_hidden('#skF_4'(k1_xboole_0, B_180), B_180) | k1_xboole_0=B_180)), inference(resolution, [status(thm)], [c_34, c_2028])).
% 12.17/5.71  tff(c_2102, plain, (![B_180, B_4]: (r2_hidden('#skF_4'(k1_xboole_0, B_180), B_4) | ~r1_tarski(B_180, B_4) | k1_xboole_0=B_180)), inference(resolution, [status(thm)], [c_2053, c_4])).
% 12.17/5.71  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.17/5.71  tff(c_2392, plain, (![A_189, B_190]: (~r2_hidden('#skF_4'(k1_xboole_0, k4_xboole_0(A_189, B_190)), B_190) | k4_xboole_0(A_189, B_190)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2053, c_12])).
% 12.17/5.71  tff(c_2437, plain, (![A_189, B_4]: (~r1_tarski(k4_xboole_0(A_189, B_4), B_4) | k4_xboole_0(A_189, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2102, c_2392])).
% 12.17/5.71  tff(c_35104, plain, (![A_741]: (k4_xboole_0(A_741, k1_relat_1('#skF_7'))=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_741, k1_relat_1('#skF_7')), '#skF_6'))), inference(resolution, [status(thm)], [c_35087, c_2437])).
% 12.17/5.71  tff(c_35132, plain, (k4_xboole_0('#skF_6', k1_relat_1('#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1502, c_35104])).
% 12.17/5.71  tff(c_38, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.17/5.71  tff(c_35546, plain, (k3_xboole_0('#skF_6', k1_relat_1('#skF_7'))=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35132, c_38])).
% 12.17/5.71  tff(c_35662, plain, (k3_xboole_0('#skF_6', k1_relat_1('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_35546])).
% 12.17/5.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.17/5.71  tff(c_303, plain, (![B_58, A_59]: (k3_xboole_0(k1_relat_1(B_58), A_59)=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.17/5.71  tff(c_327, plain, (![B_2, B_58]: (k3_xboole_0(B_2, k1_relat_1(B_58))=k1_relat_1(k7_relat_1(B_58, B_2)) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_303])).
% 12.17/5.71  tff(c_35904, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))='#skF_6' | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_35662, c_327])).
% 12.17/5.71  tff(c_35990, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_35904])).
% 12.17/5.71  tff(c_35992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_35990])).
% 12.17/5.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.71  
% 12.17/5.71  Inference rules
% 12.17/5.71  ----------------------
% 12.17/5.71  #Ref     : 0
% 12.17/5.71  #Sup     : 8990
% 12.17/5.71  #Fact    : 0
% 12.17/5.71  #Define  : 0
% 12.17/5.71  #Split   : 0
% 12.17/5.71  #Chain   : 0
% 12.17/5.71  #Close   : 0
% 12.17/5.71  
% 12.17/5.71  Ordering : KBO
% 12.17/5.71  
% 12.17/5.71  Simplification rules
% 12.17/5.71  ----------------------
% 12.17/5.71  #Subsume      : 2333
% 12.17/5.71  #Demod        : 9187
% 12.17/5.71  #Tautology    : 2979
% 12.17/5.71  #SimpNegUnit  : 1
% 12.17/5.71  #BackRed      : 0
% 12.17/5.71  
% 12.17/5.71  #Partial instantiations: 0
% 12.17/5.71  #Strategies tried      : 1
% 12.17/5.71  
% 12.17/5.71  Timing (in seconds)
% 12.17/5.71  ----------------------
% 12.17/5.71  Preprocessing        : 0.32
% 12.17/5.71  Parsing              : 0.16
% 12.17/5.71  CNF conversion       : 0.02
% 12.17/5.71  Main loop            : 4.61
% 12.17/5.71  Inferencing          : 0.90
% 12.17/5.71  Reduction            : 2.04
% 12.17/5.71  Demodulation         : 1.75
% 12.17/5.71  BG Simplification    : 0.11
% 12.17/5.71  Subsumption          : 1.28
% 12.17/5.71  Abstraction          : 0.16
% 12.17/5.71  MUC search           : 0.00
% 12.17/5.71  Cooper               : 0.00
% 12.17/5.71  Total                : 4.96
% 12.17/5.71  Index Insertion      : 0.00
% 12.17/5.71  Index Deletion       : 0.00
% 12.17/5.71  Index Matching       : 0.00
% 12.17/5.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
