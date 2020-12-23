%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:25 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   74 (  90 expanded)
%              Number of leaves         :   39 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 117 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_80,plain,(
    '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_78,plain,(
    '#skF_6' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_66,plain,(
    ! [A_69,B_70] :
      ( r1_xboole_0(k1_tarski(A_69),B_70)
      | r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_475,plain,(
    ! [A_128,B_129,C_130] :
      ( ~ r1_xboole_0(A_128,B_129)
      | ~ r2_hidden(C_130,k3_xboole_0(A_128,B_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_560,plain,(
    ! [A_137,B_138] :
      ( ~ r1_xboole_0(A_137,B_138)
      | v1_xboole_0(k3_xboole_0(A_137,B_138)) ) ),
    inference(resolution,[status(thm)],[c_8,c_475])).

tff(c_1086,plain,(
    ! [B_167,A_168] :
      ( ~ r1_xboole_0(B_167,A_168)
      | v1_xboole_0(k3_xboole_0(A_168,B_167)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_560])).

tff(c_882,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_2'(A_153,B_154),k3_xboole_0(A_153,B_154))
      | r1_xboole_0(A_153,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_911,plain,(
    ! [A_153,B_154] :
      ( ~ v1_xboole_0(k3_xboole_0(A_153,B_154))
      | r1_xboole_0(A_153,B_154) ) ),
    inference(resolution,[status(thm)],[c_882,c_6])).

tff(c_1122,plain,(
    ! [A_169,B_170] :
      ( r1_xboole_0(A_169,B_170)
      | ~ r1_xboole_0(B_170,A_169) ) ),
    inference(resolution,[status(thm)],[c_1086,c_911])).

tff(c_1134,plain,(
    ! [B_70,A_69] :
      ( r1_xboole_0(B_70,k1_tarski(A_69))
      | r2_hidden(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_66,c_1122])).

tff(c_115,plain,(
    ! [A_87] : k2_tarski(A_87,A_87) = k1_tarski(A_87) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [D_36,B_32] : r2_hidden(D_36,k2_tarski(D_36,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_105,plain,(
    ! [B_83,A_84] :
      ( ~ r2_hidden(B_83,A_84)
      | ~ v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [D_36,B_32] : ~ v1_xboole_0(k2_tarski(D_36,B_32)) ),
    inference(resolution,[status(thm)],[c_36,c_105])).

tff(c_120,plain,(
    ! [A_87] : ~ v1_xboole_0(k1_tarski(A_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_112])).

tff(c_74,plain,(
    ! [B_72,C_73] : r1_tarski(k1_tarski(B_72),k2_tarski(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_82,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_238,plain,(
    ! [A_105,B_106] :
      ( k3_xboole_0(A_105,B_106) = A_105
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_267,plain,(
    k3_xboole_0(k2_tarski('#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9')) = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_238])).

tff(c_289,plain,(
    k3_xboole_0(k2_tarski('#skF_8','#skF_9'),k2_tarski('#skF_6','#skF_7')) = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_4])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_tarski(A_20,B_21)
      | ~ r1_tarski(A_20,k3_xboole_0(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1560,plain,(
    ! [A_212] :
      ( r1_tarski(A_212,k2_tarski('#skF_8','#skF_9'))
      | ~ r1_tarski(A_212,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_20])).

tff(c_1580,plain,(
    r1_tarski(k1_tarski('#skF_6'),k2_tarski('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_74,c_1560])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1590,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k2_tarski('#skF_8','#skF_9')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_1580,c_22])).

tff(c_581,plain,(
    ! [B_4,A_3] :
      ( ~ r1_xboole_0(B_4,A_3)
      | v1_xboole_0(k3_xboole_0(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_560])).

tff(c_2127,plain,
    ( ~ r1_xboole_0(k2_tarski('#skF_8','#skF_9'),k1_tarski('#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1590,c_581])).

tff(c_2151,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_8','#skF_9'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_2127])).

tff(c_2158,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_1134,c_2151])).

tff(c_32,plain,(
    ! [D_36,B_32,A_31] :
      ( D_36 = B_32
      | D_36 = A_31
      | ~ r2_hidden(D_36,k2_tarski(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2161,plain,
    ( '#skF_6' = '#skF_9'
    | '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2158,c_32])).

tff(c_2168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_2161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.67  
% 3.79/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 3.79/1.67  
% 3.79/1.67  %Foreground sorts:
% 3.79/1.67  
% 3.79/1.67  
% 3.79/1.67  %Background operators:
% 3.79/1.67  
% 3.79/1.67  
% 3.79/1.67  %Foreground operators:
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.79/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.79/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.79/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.79/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.79/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.79/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.79/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.79/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.79/1.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.79/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.79/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.79/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff('#skF_9', type, '#skF_9': $i).
% 3.79/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff('#skF_8', type, '#skF_8': $i).
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.67  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.79/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.79/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.79/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.79/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/1.67  
% 3.79/1.68  tff(f_132, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.79/1.68  tff(f_107, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.79/1.68  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.79/1.68  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.79/1.68  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.79/1.68  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.79/1.68  tff(f_86, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.79/1.68  tff(f_122, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.79/1.68  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.79/1.68  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.79/1.68  tff(c_80, plain, ('#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.79/1.68  tff(c_78, plain, ('#skF_6'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.79/1.68  tff(c_66, plain, (![A_69, B_70]: (r1_xboole_0(k1_tarski(A_69), B_70) | r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.68  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.79/1.68  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.68  tff(c_475, plain, (![A_128, B_129, C_130]: (~r1_xboole_0(A_128, B_129) | ~r2_hidden(C_130, k3_xboole_0(A_128, B_129)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.68  tff(c_560, plain, (![A_137, B_138]: (~r1_xboole_0(A_137, B_138) | v1_xboole_0(k3_xboole_0(A_137, B_138)))), inference(resolution, [status(thm)], [c_8, c_475])).
% 3.79/1.68  tff(c_1086, plain, (![B_167, A_168]: (~r1_xboole_0(B_167, A_168) | v1_xboole_0(k3_xboole_0(A_168, B_167)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_560])).
% 3.79/1.68  tff(c_882, plain, (![A_153, B_154]: (r2_hidden('#skF_2'(A_153, B_154), k3_xboole_0(A_153, B_154)) | r1_xboole_0(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.68  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.68  tff(c_911, plain, (![A_153, B_154]: (~v1_xboole_0(k3_xboole_0(A_153, B_154)) | r1_xboole_0(A_153, B_154))), inference(resolution, [status(thm)], [c_882, c_6])).
% 3.79/1.68  tff(c_1122, plain, (![A_169, B_170]: (r1_xboole_0(A_169, B_170) | ~r1_xboole_0(B_170, A_169))), inference(resolution, [status(thm)], [c_1086, c_911])).
% 3.79/1.68  tff(c_1134, plain, (![B_70, A_69]: (r1_xboole_0(B_70, k1_tarski(A_69)) | r2_hidden(A_69, B_70))), inference(resolution, [status(thm)], [c_66, c_1122])).
% 3.79/1.68  tff(c_115, plain, (![A_87]: (k2_tarski(A_87, A_87)=k1_tarski(A_87))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.79/1.68  tff(c_36, plain, (![D_36, B_32]: (r2_hidden(D_36, k2_tarski(D_36, B_32)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.79/1.68  tff(c_105, plain, (![B_83, A_84]: (~r2_hidden(B_83, A_84) | ~v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.68  tff(c_112, plain, (![D_36, B_32]: (~v1_xboole_0(k2_tarski(D_36, B_32)))), inference(resolution, [status(thm)], [c_36, c_105])).
% 3.79/1.68  tff(c_120, plain, (![A_87]: (~v1_xboole_0(k1_tarski(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_112])).
% 3.79/1.68  tff(c_74, plain, (![B_72, C_73]: (r1_tarski(k1_tarski(B_72), k2_tarski(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.79/1.68  tff(c_82, plain, (r1_tarski(k2_tarski('#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.79/1.68  tff(c_238, plain, (![A_105, B_106]: (k3_xboole_0(A_105, B_106)=A_105 | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.79/1.68  tff(c_267, plain, (k3_xboole_0(k2_tarski('#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9'))=k2_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_82, c_238])).
% 3.79/1.68  tff(c_289, plain, (k3_xboole_0(k2_tarski('#skF_8', '#skF_9'), k2_tarski('#skF_6', '#skF_7'))=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_267, c_4])).
% 3.79/1.68  tff(c_20, plain, (![A_20, B_21, C_22]: (r1_tarski(A_20, B_21) | ~r1_tarski(A_20, k3_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.79/1.68  tff(c_1560, plain, (![A_212]: (r1_tarski(A_212, k2_tarski('#skF_8', '#skF_9')) | ~r1_tarski(A_212, k2_tarski('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_289, c_20])).
% 3.79/1.68  tff(c_1580, plain, (r1_tarski(k1_tarski('#skF_6'), k2_tarski('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_74, c_1560])).
% 3.79/1.68  tff(c_22, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.79/1.68  tff(c_1590, plain, (k3_xboole_0(k1_tarski('#skF_6'), k2_tarski('#skF_8', '#skF_9'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_1580, c_22])).
% 3.79/1.68  tff(c_581, plain, (![B_4, A_3]: (~r1_xboole_0(B_4, A_3) | v1_xboole_0(k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_560])).
% 3.79/1.68  tff(c_2127, plain, (~r1_xboole_0(k2_tarski('#skF_8', '#skF_9'), k1_tarski('#skF_6')) | v1_xboole_0(k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1590, c_581])).
% 3.79/1.68  tff(c_2151, plain, (~r1_xboole_0(k2_tarski('#skF_8', '#skF_9'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_120, c_2127])).
% 3.79/1.68  tff(c_2158, plain, (r2_hidden('#skF_6', k2_tarski('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_1134, c_2151])).
% 3.79/1.68  tff(c_32, plain, (![D_36, B_32, A_31]: (D_36=B_32 | D_36=A_31 | ~r2_hidden(D_36, k2_tarski(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.79/1.68  tff(c_2161, plain, ('#skF_6'='#skF_9' | '#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_2158, c_32])).
% 3.79/1.68  tff(c_2168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_2161])).
% 3.79/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.68  
% 3.79/1.68  Inference rules
% 3.79/1.68  ----------------------
% 3.79/1.68  #Ref     : 0
% 3.79/1.68  #Sup     : 499
% 3.79/1.68  #Fact    : 0
% 3.79/1.68  #Define  : 0
% 3.79/1.68  #Split   : 1
% 3.79/1.68  #Chain   : 0
% 3.79/1.68  #Close   : 0
% 3.79/1.68  
% 3.79/1.68  Ordering : KBO
% 3.79/1.68  
% 3.79/1.68  Simplification rules
% 3.79/1.68  ----------------------
% 3.79/1.68  #Subsume      : 92
% 3.79/1.68  #Demod        : 206
% 3.79/1.68  #Tautology    : 289
% 3.79/1.68  #SimpNegUnit  : 33
% 3.79/1.68  #BackRed      : 14
% 3.79/1.68  
% 3.79/1.68  #Partial instantiations: 0
% 3.79/1.68  #Strategies tried      : 1
% 3.79/1.68  
% 3.79/1.68  Timing (in seconds)
% 3.79/1.68  ----------------------
% 3.89/1.69  Preprocessing        : 0.35
% 3.89/1.69  Parsing              : 0.19
% 3.89/1.69  CNF conversion       : 0.02
% 3.89/1.69  Main loop            : 0.53
% 3.89/1.69  Inferencing          : 0.18
% 3.89/1.69  Reduction            : 0.20
% 3.89/1.69  Demodulation         : 0.14
% 3.89/1.69  BG Simplification    : 0.03
% 3.89/1.69  Subsumption          : 0.09
% 3.89/1.69  Abstraction          : 0.02
% 3.89/1.69  MUC search           : 0.00
% 3.89/1.69  Cooper               : 0.00
% 3.89/1.69  Total                : 0.91
% 3.89/1.69  Index Insertion      : 0.00
% 3.89/1.69  Index Deletion       : 0.00
% 3.89/1.69  Index Matching       : 0.00
% 3.89/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
