%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:05 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 111 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 243 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_58,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(c_36,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ! [A_25] :
      ( v1_ordinal1(A_25)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_38])).

tff(c_96,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_2'(A_47,B_48),A_47)
      | r1_tarski(k3_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [B_18,A_15] :
      ( r1_tarski(B_18,A_15)
      | ~ r2_hidden(B_18,A_15)
      | ~ v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_175,plain,(
    ! [A_71,B_72] :
      ( r1_tarski('#skF_2'(A_71,B_72),A_71)
      | ~ v1_ordinal1(A_71)
      | r1_tarski(k3_tarski(A_71),B_72) ) ),
    inference(resolution,[status(thm)],[c_96,c_24])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r1_tarski('#skF_2'(A_8,B_9),B_9)
      | r1_tarski(k3_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_187,plain,(
    ! [A_71] :
      ( ~ v1_ordinal1(A_71)
      | r1_tarski(k3_tarski(A_71),A_71) ) ),
    inference(resolution,[status(thm)],[c_175,c_14])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_28,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_3'(A_15),A_15)
      | v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_89,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,(
    ! [A_15,B_45] :
      ( r2_hidden('#skF_3'(A_15),B_45)
      | ~ r1_tarski(A_15,B_45)
      | v1_ordinal1(A_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_136,plain,(
    ! [C_59,B_60,A_61] :
      ( r1_tarski(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(k3_tarski(A_61),B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_516,plain,(
    ! [A_118,B_119,B_120] :
      ( r1_tarski('#skF_3'(A_118),B_119)
      | ~ r1_tarski(k3_tarski(B_120),B_119)
      | ~ r1_tarski(A_118,B_120)
      | v1_ordinal1(A_118) ) ),
    inference(resolution,[status(thm)],[c_95,c_136])).

tff(c_530,plain,(
    ! [A_121,B_122] :
      ( r1_tarski('#skF_3'(A_121),k3_tarski(B_122))
      | ~ r1_tarski(A_121,B_122)
      | v1_ordinal1(A_121) ) ),
    inference(resolution,[status(thm)],[c_86,c_516])).

tff(c_26,plain,(
    ! [A_15] :
      ( ~ r1_tarski('#skF_3'(A_15),A_15)
      | v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_602,plain,(
    ! [B_126] :
      ( ~ r1_tarski(k3_tarski(B_126),B_126)
      | v1_ordinal1(k3_tarski(B_126)) ) ),
    inference(resolution,[status(thm)],[c_530,c_26])).

tff(c_619,plain,(
    ! [A_71] :
      ( v1_ordinal1(k3_tarski(A_71))
      | ~ v1_ordinal1(A_71) ) ),
    inference(resolution,[status(thm)],[c_187,c_602])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(A_49,B_50)
      | ~ r2_xboole_0(A_49,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v1_ordinal1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_255,plain,(
    ! [A_85,B_86] :
      ( r2_hidden(A_85,B_86)
      | ~ v3_ordinal1(B_86)
      | ~ v1_ordinal1(A_85)
      | B_86 = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( v3_ordinal1(A_22)
      | ~ r2_hidden(A_22,B_23)
      | ~ v3_ordinal1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_275,plain,(
    ! [A_87,B_88] :
      ( v3_ordinal1(A_87)
      | ~ v3_ordinal1(B_88)
      | ~ v1_ordinal1(A_87)
      | B_88 = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_255,c_32])).

tff(c_742,plain,(
    ! [A_135] :
      ( v3_ordinal1(k3_tarski(A_135))
      | ~ v3_ordinal1(A_135)
      | ~ v1_ordinal1(k3_tarski(A_135))
      | k3_tarski(A_135) = A_135
      | ~ v1_ordinal1(A_135) ) ),
    inference(resolution,[status(thm)],[c_187,c_275])).

tff(c_34,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_751,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1(k3_tarski('#skF_4'))
    | k3_tarski('#skF_4') = '#skF_4'
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_742,c_34])).

tff(c_756,plain,
    ( ~ v1_ordinal1(k3_tarski('#skF_4'))
    | k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_751])).

tff(c_806,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_812,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_619,c_806])).

tff(c_819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_812])).

tff(c_820,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_822,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_34])).

tff(c_825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:49:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.49  
% 3.09/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.50  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.09/1.50  
% 3.09/1.50  %Foreground sorts:
% 3.09/1.50  
% 3.09/1.50  
% 3.09/1.50  %Background operators:
% 3.09/1.50  
% 3.09/1.50  
% 3.09/1.50  %Foreground operators:
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.50  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 3.09/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.50  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.09/1.50  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 3.09/1.50  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.09/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.50  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.50  
% 3.09/1.51  tff(f_85, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 3.09/1.51  tff(f_58, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 3.09/1.51  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 3.09/1.51  tff(f_65, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 3.09/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.09/1.51  tff(f_52, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 3.09/1.51  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.09/1.51  tff(f_74, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 3.09/1.51  tff(f_80, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 3.09/1.51  tff(c_36, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.09/1.51  tff(c_38, plain, (![A_25]: (v1_ordinal1(A_25) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.51  tff(c_42, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_38])).
% 3.09/1.51  tff(c_96, plain, (![A_47, B_48]: (r2_hidden('#skF_2'(A_47, B_48), A_47) | r1_tarski(k3_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.09/1.51  tff(c_24, plain, (![B_18, A_15]: (r1_tarski(B_18, A_15) | ~r2_hidden(B_18, A_15) | ~v1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.51  tff(c_175, plain, (![A_71, B_72]: (r1_tarski('#skF_2'(A_71, B_72), A_71) | ~v1_ordinal1(A_71) | r1_tarski(k3_tarski(A_71), B_72))), inference(resolution, [status(thm)], [c_96, c_24])).
% 3.09/1.51  tff(c_14, plain, (![A_8, B_9]: (~r1_tarski('#skF_2'(A_8, B_9), B_9) | r1_tarski(k3_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.09/1.51  tff(c_187, plain, (![A_71]: (~v1_ordinal1(A_71) | r1_tarski(k3_tarski(A_71), A_71))), inference(resolution, [status(thm)], [c_175, c_14])).
% 3.09/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.09/1.51  tff(c_81, plain, (![A_39, B_40]: (~r2_hidden('#skF_1'(A_39, B_40), B_40) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.09/1.51  tff(c_86, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_81])).
% 3.09/1.51  tff(c_28, plain, (![A_15]: (r2_hidden('#skF_3'(A_15), A_15) | v1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.51  tff(c_89, plain, (![C_44, B_45, A_46]: (r2_hidden(C_44, B_45) | ~r2_hidden(C_44, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.09/1.51  tff(c_95, plain, (![A_15, B_45]: (r2_hidden('#skF_3'(A_15), B_45) | ~r1_tarski(A_15, B_45) | v1_ordinal1(A_15))), inference(resolution, [status(thm)], [c_28, c_89])).
% 3.09/1.51  tff(c_136, plain, (![C_59, B_60, A_61]: (r1_tarski(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(k3_tarski(A_61), B_60))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.09/1.51  tff(c_516, plain, (![A_118, B_119, B_120]: (r1_tarski('#skF_3'(A_118), B_119) | ~r1_tarski(k3_tarski(B_120), B_119) | ~r1_tarski(A_118, B_120) | v1_ordinal1(A_118))), inference(resolution, [status(thm)], [c_95, c_136])).
% 3.09/1.51  tff(c_530, plain, (![A_121, B_122]: (r1_tarski('#skF_3'(A_121), k3_tarski(B_122)) | ~r1_tarski(A_121, B_122) | v1_ordinal1(A_121))), inference(resolution, [status(thm)], [c_86, c_516])).
% 3.09/1.51  tff(c_26, plain, (![A_15]: (~r1_tarski('#skF_3'(A_15), A_15) | v1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.51  tff(c_602, plain, (![B_126]: (~r1_tarski(k3_tarski(B_126), B_126) | v1_ordinal1(k3_tarski(B_126)))), inference(resolution, [status(thm)], [c_530, c_26])).
% 3.09/1.51  tff(c_619, plain, (![A_71]: (v1_ordinal1(k3_tarski(A_71)) | ~v1_ordinal1(A_71))), inference(resolution, [status(thm)], [c_187, c_602])).
% 3.09/1.51  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.09/1.51  tff(c_108, plain, (![A_49, B_50]: (r2_hidden(A_49, B_50) | ~r2_xboole_0(A_49, B_50) | ~v3_ordinal1(B_50) | ~v1_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.09/1.51  tff(c_255, plain, (![A_85, B_86]: (r2_hidden(A_85, B_86) | ~v3_ordinal1(B_86) | ~v1_ordinal1(A_85) | B_86=A_85 | ~r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_8, c_108])).
% 3.09/1.51  tff(c_32, plain, (![A_22, B_23]: (v3_ordinal1(A_22) | ~r2_hidden(A_22, B_23) | ~v3_ordinal1(B_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.51  tff(c_275, plain, (![A_87, B_88]: (v3_ordinal1(A_87) | ~v3_ordinal1(B_88) | ~v1_ordinal1(A_87) | B_88=A_87 | ~r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_255, c_32])).
% 3.09/1.51  tff(c_742, plain, (![A_135]: (v3_ordinal1(k3_tarski(A_135)) | ~v3_ordinal1(A_135) | ~v1_ordinal1(k3_tarski(A_135)) | k3_tarski(A_135)=A_135 | ~v1_ordinal1(A_135))), inference(resolution, [status(thm)], [c_187, c_275])).
% 3.09/1.51  tff(c_34, plain, (~v3_ordinal1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.09/1.51  tff(c_751, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1(k3_tarski('#skF_4')) | k3_tarski('#skF_4')='#skF_4' | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_742, c_34])).
% 3.09/1.51  tff(c_756, plain, (~v1_ordinal1(k3_tarski('#skF_4')) | k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_751])).
% 3.09/1.51  tff(c_806, plain, (~v1_ordinal1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_756])).
% 3.09/1.51  tff(c_812, plain, (~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_619, c_806])).
% 3.09/1.51  tff(c_819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_812])).
% 3.09/1.51  tff(c_820, plain, (k3_tarski('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_756])).
% 3.09/1.51  tff(c_822, plain, (~v3_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_34])).
% 3.09/1.51  tff(c_825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_822])).
% 3.09/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.51  
% 3.09/1.51  Inference rules
% 3.09/1.51  ----------------------
% 3.09/1.51  #Ref     : 0
% 3.09/1.51  #Sup     : 198
% 3.09/1.51  #Fact    : 0
% 3.09/1.51  #Define  : 0
% 3.09/1.51  #Split   : 1
% 3.09/1.51  #Chain   : 0
% 3.09/1.51  #Close   : 0
% 3.09/1.51  
% 3.09/1.51  Ordering : KBO
% 3.09/1.51  
% 3.09/1.51  Simplification rules
% 3.09/1.51  ----------------------
% 3.09/1.51  #Subsume      : 29
% 3.09/1.51  #Demod        : 9
% 3.09/1.51  #Tautology    : 11
% 3.09/1.51  #SimpNegUnit  : 0
% 3.09/1.51  #BackRed      : 1
% 3.09/1.51  
% 3.09/1.51  #Partial instantiations: 0
% 3.09/1.51  #Strategies tried      : 1
% 3.09/1.51  
% 3.09/1.51  Timing (in seconds)
% 3.09/1.51  ----------------------
% 3.09/1.51  Preprocessing        : 0.30
% 3.09/1.51  Parsing              : 0.17
% 3.09/1.51  CNF conversion       : 0.02
% 3.09/1.51  Main loop            : 0.43
% 3.09/1.51  Inferencing          : 0.17
% 3.09/1.51  Reduction            : 0.09
% 3.09/1.51  Demodulation         : 0.06
% 3.09/1.51  BG Simplification    : 0.02
% 3.09/1.51  Subsumption          : 0.12
% 3.09/1.51  Abstraction          : 0.02
% 3.09/1.51  MUC search           : 0.00
% 3.09/1.51  Cooper               : 0.00
% 3.09/1.51  Total                : 0.76
% 3.09/1.51  Index Insertion      : 0.00
% 3.09/1.51  Index Deletion       : 0.00
% 3.09/1.51  Index Matching       : 0.00
% 3.09/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
