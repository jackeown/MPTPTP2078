%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:39 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 152 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 332 expanded)
%              Number of equality atoms :   30 ( 106 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_79,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_87,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_42])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_204,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_1'(A_73,B_74,C_75),A_73)
      | r2_hidden('#skF_2'(A_73,B_74,C_75),C_75)
      | k4_xboole_0(A_73,B_74) = C_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_255,plain,(
    ! [A_73,B_74,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_73,B_74,k4_xboole_0(A_1,B_2)),A_1)
      | r2_hidden('#skF_1'(A_73,B_74,k4_xboole_0(A_1,B_2)),A_73)
      | k4_xboole_0(A_73,B_74) = k4_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_204,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1698,plain,(
    ! [A_161,B_162,A_163,B_164] :
      ( ~ r2_hidden('#skF_2'(A_161,B_162,k4_xboole_0(A_163,B_164)),B_164)
      | r2_hidden('#skF_1'(A_161,B_162,k4_xboole_0(A_163,B_164)),A_161)
      | k4_xboole_0(A_163,B_164) = k4_xboole_0(A_161,B_162) ) ),
    inference(resolution,[status(thm)],[c_204,c_4])).

tff(c_1707,plain,(
    ! [A_73,B_74,A_1] :
      ( r2_hidden('#skF_1'(A_73,B_74,k4_xboole_0(A_1,A_1)),A_73)
      | k4_xboole_0(A_73,B_74) = k4_xboole_0(A_1,A_1) ) ),
    inference(resolution,[status(thm)],[c_255,c_1698])).

tff(c_1737,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74,k1_xboole_0),A_73)
      | k4_xboole_0(A_73,B_74) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_1707])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,k2_relat_1(B_22))
      | k10_relat_1(B_22,k1_tarski(A_21)) = k1_xboole_0
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_195,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r2_hidden('#skF_1'(A_70,B_71,C_72),B_71)
      | r2_hidden('#skF_2'(A_70,B_71,C_72),C_72)
      | k4_xboole_0(A_70,B_71) = C_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2941,plain,(
    ! [A_237,B_238,C_239] :
      ( r2_hidden('#skF_2'(A_237,k2_relat_1(B_238),C_239),C_239)
      | k4_xboole_0(A_237,k2_relat_1(B_238)) = C_239
      | k10_relat_1(B_238,k1_tarski('#skF_1'(A_237,k2_relat_1(B_238),C_239))) = k1_xboole_0
      | ~ v1_relat_1(B_238) ) ),
    inference(resolution,[status(thm)],[c_38,c_195])).

tff(c_44,plain,(
    ! [C_24] :
      ( k10_relat_1('#skF_4',k1_tarski(C_24)) != k1_xboole_0
      | ~ r2_hidden(C_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2988,plain,(
    ! [A_237,C_239] :
      ( ~ r2_hidden('#skF_1'(A_237,k2_relat_1('#skF_4'),C_239),'#skF_3')
      | r2_hidden('#skF_2'(A_237,k2_relat_1('#skF_4'),C_239),C_239)
      | k4_xboole_0(A_237,k2_relat_1('#skF_4')) = C_239
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2941,c_44])).

tff(c_3196,plain,(
    ! [A_248,C_249] :
      ( ~ r2_hidden('#skF_1'(A_248,k2_relat_1('#skF_4'),C_249),'#skF_3')
      | r2_hidden('#skF_2'(A_248,k2_relat_1('#skF_4'),C_249),C_249)
      | k4_xboole_0(A_248,k2_relat_1('#skF_4')) = C_249 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2988])).

tff(c_3205,plain,
    ( r2_hidden('#skF_2'('#skF_3',k2_relat_1('#skF_4'),k1_xboole_0),k1_xboole_0)
    | k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1737,c_3196])).

tff(c_3220,plain,(
    r2_hidden('#skF_2'('#skF_3',k2_relat_1('#skF_4'),k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_87,c_3205])).

tff(c_89,plain,(
    ! [D_35,A_36,B_37] :
      ( r2_hidden(D_35,A_36)
      | ~ r2_hidden(D_35,k4_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [D_35,B_8] :
      ( r2_hidden(D_35,B_8)
      | ~ r2_hidden(D_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_89])).

tff(c_3229,plain,(
    ! [B_8] : r2_hidden('#skF_2'('#skF_3',k2_relat_1('#skF_4'),k1_xboole_0),B_8) ),
    inference(resolution,[status(thm)],[c_3220,c_92])).

tff(c_3231,plain,(
    ! [B_250] : r2_hidden('#skF_2'('#skF_3',k2_relat_1('#skF_4'),k1_xboole_0),B_250) ),
    inference(resolution,[status(thm)],[c_3220,c_92])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_246,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74,A_73),A_73)
      | k4_xboole_0(A_73,B_74) = A_73 ) ),
    inference(resolution,[status(thm)],[c_204,c_14])).

tff(c_407,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_1'(A_92,B_93,C_94),A_92)
      | r2_hidden('#skF_2'(A_92,B_93,C_94),B_93)
      | ~ r2_hidden('#skF_2'(A_92,B_93,C_94),A_92)
      | k4_xboole_0(A_92,B_93) = C_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_526,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_2'(A_100,B_101,A_100),B_101)
      | ~ r2_hidden('#skF_2'(A_100,B_101,A_100),A_100)
      | k4_xboole_0(A_100,B_101) = A_100 ) ),
    inference(resolution,[status(thm)],[c_407,c_8])).

tff(c_564,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_2'(A_105,B_106,A_105),B_106)
      | k4_xboole_0(A_105,B_106) = A_105 ) ),
    inference(resolution,[status(thm)],[c_246,c_526])).

tff(c_684,plain,(
    ! [A_110,A_111,B_112] :
      ( ~ r2_hidden('#skF_2'(A_110,k4_xboole_0(A_111,B_112),A_110),B_112)
      | k4_xboole_0(A_110,k4_xboole_0(A_111,B_112)) = A_110 ) ),
    inference(resolution,[status(thm)],[c_564,c_4])).

tff(c_811,plain,(
    ! [A_117,A_118] : k4_xboole_0(A_117,k4_xboole_0(A_118,A_117)) = A_117 ),
    inference(resolution,[status(thm)],[c_246,c_684])).

tff(c_844,plain,(
    ! [D_6,A_118,A_117] :
      ( ~ r2_hidden(D_6,k4_xboole_0(A_118,A_117))
      | ~ r2_hidden(D_6,A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_4])).

tff(c_3235,plain,(
    ! [A_117] : ~ r2_hidden('#skF_2'('#skF_3',k2_relat_1('#skF_4'),k1_xboole_0),A_117) ),
    inference(resolution,[status(thm)],[c_3231,c_844])).

tff(c_3253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3229,c_3235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:56:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.77  
% 4.13/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.77  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 4.13/1.77  
% 4.13/1.77  %Foreground sorts:
% 4.13/1.77  
% 4.13/1.77  
% 4.13/1.77  %Background operators:
% 4.13/1.77  
% 4.13/1.77  
% 4.13/1.77  %Foreground operators:
% 4.13/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.13/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.13/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.13/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.13/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.13/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.13/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.13/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.13/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.77  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.13/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.77  
% 4.52/1.79  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.52/1.79  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_1)).
% 4.52/1.79  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.52/1.79  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.52/1.79  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 4.52/1.79  tff(c_79, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.52/1.79  tff(c_42, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.52/1.79  tff(c_87, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_79, c_42])).
% 4.52/1.79  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.52/1.79  tff(c_67, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.52/1.79  tff(c_71, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_67])).
% 4.52/1.79  tff(c_204, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_1'(A_73, B_74, C_75), A_73) | r2_hidden('#skF_2'(A_73, B_74, C_75), C_75) | k4_xboole_0(A_73, B_74)=C_75)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.79  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.79  tff(c_255, plain, (![A_73, B_74, A_1, B_2]: (r2_hidden('#skF_2'(A_73, B_74, k4_xboole_0(A_1, B_2)), A_1) | r2_hidden('#skF_1'(A_73, B_74, k4_xboole_0(A_1, B_2)), A_73) | k4_xboole_0(A_73, B_74)=k4_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_204, c_6])).
% 4.52/1.79  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.79  tff(c_1698, plain, (![A_161, B_162, A_163, B_164]: (~r2_hidden('#skF_2'(A_161, B_162, k4_xboole_0(A_163, B_164)), B_164) | r2_hidden('#skF_1'(A_161, B_162, k4_xboole_0(A_163, B_164)), A_161) | k4_xboole_0(A_163, B_164)=k4_xboole_0(A_161, B_162))), inference(resolution, [status(thm)], [c_204, c_4])).
% 4.52/1.79  tff(c_1707, plain, (![A_73, B_74, A_1]: (r2_hidden('#skF_1'(A_73, B_74, k4_xboole_0(A_1, A_1)), A_73) | k4_xboole_0(A_73, B_74)=k4_xboole_0(A_1, A_1))), inference(resolution, [status(thm)], [c_255, c_1698])).
% 4.52/1.79  tff(c_1737, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74, k1_xboole_0), A_73) | k4_xboole_0(A_73, B_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_1707])).
% 4.52/1.79  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.52/1.79  tff(c_38, plain, (![A_21, B_22]: (r2_hidden(A_21, k2_relat_1(B_22)) | k10_relat_1(B_22, k1_tarski(A_21))=k1_xboole_0 | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.52/1.79  tff(c_195, plain, (![A_70, B_71, C_72]: (~r2_hidden('#skF_1'(A_70, B_71, C_72), B_71) | r2_hidden('#skF_2'(A_70, B_71, C_72), C_72) | k4_xboole_0(A_70, B_71)=C_72)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.79  tff(c_2941, plain, (![A_237, B_238, C_239]: (r2_hidden('#skF_2'(A_237, k2_relat_1(B_238), C_239), C_239) | k4_xboole_0(A_237, k2_relat_1(B_238))=C_239 | k10_relat_1(B_238, k1_tarski('#skF_1'(A_237, k2_relat_1(B_238), C_239)))=k1_xboole_0 | ~v1_relat_1(B_238))), inference(resolution, [status(thm)], [c_38, c_195])).
% 4.52/1.79  tff(c_44, plain, (![C_24]: (k10_relat_1('#skF_4', k1_tarski(C_24))!=k1_xboole_0 | ~r2_hidden(C_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.52/1.79  tff(c_2988, plain, (![A_237, C_239]: (~r2_hidden('#skF_1'(A_237, k2_relat_1('#skF_4'), C_239), '#skF_3') | r2_hidden('#skF_2'(A_237, k2_relat_1('#skF_4'), C_239), C_239) | k4_xboole_0(A_237, k2_relat_1('#skF_4'))=C_239 | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2941, c_44])).
% 4.52/1.79  tff(c_3196, plain, (![A_248, C_249]: (~r2_hidden('#skF_1'(A_248, k2_relat_1('#skF_4'), C_249), '#skF_3') | r2_hidden('#skF_2'(A_248, k2_relat_1('#skF_4'), C_249), C_249) | k4_xboole_0(A_248, k2_relat_1('#skF_4'))=C_249)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2988])).
% 4.52/1.79  tff(c_3205, plain, (r2_hidden('#skF_2'('#skF_3', k2_relat_1('#skF_4'), k1_xboole_0), k1_xboole_0) | k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1737, c_3196])).
% 4.52/1.79  tff(c_3220, plain, (r2_hidden('#skF_2'('#skF_3', k2_relat_1('#skF_4'), k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_87, c_87, c_3205])).
% 4.52/1.79  tff(c_89, plain, (![D_35, A_36, B_37]: (r2_hidden(D_35, A_36) | ~r2_hidden(D_35, k4_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.79  tff(c_92, plain, (![D_35, B_8]: (r2_hidden(D_35, B_8) | ~r2_hidden(D_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_89])).
% 4.52/1.79  tff(c_3229, plain, (![B_8]: (r2_hidden('#skF_2'('#skF_3', k2_relat_1('#skF_4'), k1_xboole_0), B_8))), inference(resolution, [status(thm)], [c_3220, c_92])).
% 4.52/1.79  tff(c_3231, plain, (![B_250]: (r2_hidden('#skF_2'('#skF_3', k2_relat_1('#skF_4'), k1_xboole_0), B_250))), inference(resolution, [status(thm)], [c_3220, c_92])).
% 4.52/1.79  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.79  tff(c_246, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74, A_73), A_73) | k4_xboole_0(A_73, B_74)=A_73)), inference(resolution, [status(thm)], [c_204, c_14])).
% 4.52/1.79  tff(c_407, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_1'(A_92, B_93, C_94), A_92) | r2_hidden('#skF_2'(A_92, B_93, C_94), B_93) | ~r2_hidden('#skF_2'(A_92, B_93, C_94), A_92) | k4_xboole_0(A_92, B_93)=C_94)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.79  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.79  tff(c_526, plain, (![A_100, B_101]: (r2_hidden('#skF_2'(A_100, B_101, A_100), B_101) | ~r2_hidden('#skF_2'(A_100, B_101, A_100), A_100) | k4_xboole_0(A_100, B_101)=A_100)), inference(resolution, [status(thm)], [c_407, c_8])).
% 4.52/1.79  tff(c_564, plain, (![A_105, B_106]: (r2_hidden('#skF_2'(A_105, B_106, A_105), B_106) | k4_xboole_0(A_105, B_106)=A_105)), inference(resolution, [status(thm)], [c_246, c_526])).
% 4.52/1.79  tff(c_684, plain, (![A_110, A_111, B_112]: (~r2_hidden('#skF_2'(A_110, k4_xboole_0(A_111, B_112), A_110), B_112) | k4_xboole_0(A_110, k4_xboole_0(A_111, B_112))=A_110)), inference(resolution, [status(thm)], [c_564, c_4])).
% 4.52/1.79  tff(c_811, plain, (![A_117, A_118]: (k4_xboole_0(A_117, k4_xboole_0(A_118, A_117))=A_117)), inference(resolution, [status(thm)], [c_246, c_684])).
% 4.52/1.79  tff(c_844, plain, (![D_6, A_118, A_117]: (~r2_hidden(D_6, k4_xboole_0(A_118, A_117)) | ~r2_hidden(D_6, A_117))), inference(superposition, [status(thm), theory('equality')], [c_811, c_4])).
% 4.52/1.79  tff(c_3235, plain, (![A_117]: (~r2_hidden('#skF_2'('#skF_3', k2_relat_1('#skF_4'), k1_xboole_0), A_117))), inference(resolution, [status(thm)], [c_3231, c_844])).
% 4.52/1.79  tff(c_3253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3229, c_3235])).
% 4.52/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.79  
% 4.52/1.79  Inference rules
% 4.52/1.79  ----------------------
% 4.52/1.79  #Ref     : 0
% 4.52/1.79  #Sup     : 682
% 4.52/1.79  #Fact    : 0
% 4.52/1.79  #Define  : 0
% 4.52/1.79  #Split   : 0
% 4.52/1.79  #Chain   : 0
% 4.52/1.79  #Close   : 0
% 4.52/1.79  
% 4.52/1.79  Ordering : KBO
% 4.52/1.79  
% 4.52/1.79  Simplification rules
% 4.52/1.79  ----------------------
% 4.52/1.79  #Subsume      : 228
% 4.52/1.79  #Demod        : 639
% 4.52/1.79  #Tautology    : 283
% 4.52/1.79  #SimpNegUnit  : 1
% 4.52/1.79  #BackRed      : 1
% 4.52/1.79  
% 4.52/1.79  #Partial instantiations: 0
% 4.52/1.79  #Strategies tried      : 1
% 4.52/1.79  
% 4.52/1.79  Timing (in seconds)
% 4.52/1.79  ----------------------
% 4.52/1.79  Preprocessing        : 0.31
% 4.52/1.79  Parsing              : 0.16
% 4.52/1.79  CNF conversion       : 0.02
% 4.52/1.79  Main loop            : 0.72
% 4.52/1.79  Inferencing          : 0.27
% 4.52/1.79  Reduction            : 0.22
% 4.52/1.79  Demodulation         : 0.15
% 4.52/1.79  BG Simplification    : 0.03
% 4.52/1.79  Subsumption          : 0.16
% 4.52/1.79  Abstraction          : 0.04
% 4.52/1.79  MUC search           : 0.00
% 4.52/1.79  Cooper               : 0.00
% 4.52/1.79  Total                : 1.07
% 4.52/1.79  Index Insertion      : 0.00
% 4.52/1.79  Index Deletion       : 0.00
% 4.52/1.79  Index Matching       : 0.00
% 4.52/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
