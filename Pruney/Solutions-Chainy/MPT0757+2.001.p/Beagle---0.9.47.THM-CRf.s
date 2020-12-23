%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:31 EST 2020

% Result     : Theorem 31.13s
% Output     : CNFRefutation 31.13s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 143 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 ( 403 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ~ ( ~ r2_xboole_0(A,B)
                & A != B
                & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_60,axiom,(
    ! [A] :
    ? [B] :
    ! [C] :
      ( r2_hidden(C,B)
    <=> ( r2_hidden(C,A)
        & v3_ordinal1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_51,plain,(
    ! [A_40,B_41] :
      ( r2_xboole_0(A_40,B_41)
      | B_41 = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ~ r2_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_36])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_64])).

tff(c_44,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    ! [B_24,A_22] :
      ( r2_hidden(B_24,A_22)
      | B_24 = A_22
      | r2_hidden(A_22,B_24)
      | ~ v3_ordinal1(B_24)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_89,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( v3_ordinal1(A_20)
      | ~ r2_hidden(A_20,B_21)
      | ~ v3_ordinal1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_109,plain,(
    ! [A_48,B_49] :
      ( v3_ordinal1('#skF_1'(A_48,B_49))
      | ~ v3_ordinal1(A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_89,c_30])).

tff(c_118,plain,(
    ! [C_56,A_57] :
      ( r2_hidden(C_56,'#skF_2'(A_57))
      | ~ v3_ordinal1(C_56)
      | ~ r2_hidden(C_56,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2376,plain,(
    ! [A_202,A_203] :
      ( r1_tarski(A_202,'#skF_2'(A_203))
      | ~ v3_ordinal1('#skF_1'(A_202,'#skF_2'(A_203)))
      | ~ r2_hidden('#skF_1'(A_202,'#skF_2'(A_203)),A_203) ) ),
    inference(resolution,[status(thm)],[c_118,c_6])).

tff(c_22696,plain,(
    ! [A_685,B_686] :
      ( r1_tarski(A_685,'#skF_2'(B_686))
      | r2_hidden(B_686,'#skF_1'(A_685,'#skF_2'(B_686)))
      | '#skF_1'(A_685,'#skF_2'(B_686)) = B_686
      | ~ v3_ordinal1(B_686)
      | ~ v3_ordinal1('#skF_1'(A_685,'#skF_2'(B_686))) ) ),
    inference(resolution,[status(thm)],[c_32,c_2376])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [C_58,A_59,B_60] :
      ( ~ r2_hidden(C_58,A_59)
      | ~ r2_hidden(B_60,C_58)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_148,plain,(
    ! [B_60,A_3,B_4] :
      ( ~ r2_hidden(B_60,'#skF_1'(A_3,B_4))
      | ~ r2_hidden(A_3,B_60)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_42885,plain,(
    ! [A_973,B_974] :
      ( ~ r2_hidden(A_973,B_974)
      | r1_tarski(A_973,'#skF_2'(B_974))
      | '#skF_1'(A_973,'#skF_2'(B_974)) = B_974
      | ~ v3_ordinal1(B_974)
      | ~ v3_ordinal1('#skF_1'(A_973,'#skF_2'(B_974))) ) ),
    inference(resolution,[status(thm)],[c_22696,c_148])).

tff(c_42904,plain,(
    ! [A_975,B_976] :
      ( ~ r2_hidden(A_975,B_976)
      | '#skF_1'(A_975,'#skF_2'(B_976)) = B_976
      | ~ v3_ordinal1(B_976)
      | ~ v3_ordinal1(A_975)
      | r1_tarski(A_975,'#skF_2'(B_976)) ) ),
    inference(resolution,[status(thm)],[c_109,c_42885])).

tff(c_113,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_279,plain,(
    ! [A_74,B_75,B_76] :
      ( r2_hidden('#skF_1'(A_74,B_75),B_76)
      | ~ r1_tarski(A_74,B_76)
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_28,plain,(
    ! [C_19,A_14] :
      ( r2_hidden(C_19,A_14)
      | ~ r2_hidden(C_19,'#skF_2'(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_466,plain,(
    ! [A_98,B_99,A_100] :
      ( r2_hidden('#skF_1'(A_98,B_99),A_100)
      | ~ r1_tarski(A_98,'#skF_2'(A_100))
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_279,c_28])).

tff(c_513,plain,(
    ! [A_98,A_100] :
      ( ~ r1_tarski(A_98,'#skF_2'(A_100))
      | r1_tarski(A_98,A_100) ) ),
    inference(resolution,[status(thm)],[c_466,c_6])).

tff(c_43157,plain,(
    ! [A_977,B_978] :
      ( r1_tarski(A_977,B_978)
      | ~ r2_hidden(A_977,B_978)
      | '#skF_1'(A_977,'#skF_2'(B_978)) = B_978
      | ~ v3_ordinal1(B_978)
      | ~ v3_ordinal1(A_977) ) ),
    inference(resolution,[status(thm)],[c_42904,c_513])).

tff(c_59721,plain,(
    ! [B_1162,A_1163] :
      ( r2_hidden(B_1162,A_1163)
      | r1_tarski(A_1163,'#skF_2'(B_1162))
      | r1_tarski(A_1163,B_1162)
      | ~ r2_hidden(A_1163,B_1162)
      | ~ v3_ordinal1(B_1162)
      | ~ v3_ordinal1(A_1163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43157,c_8])).

tff(c_60030,plain,(
    ! [B_1164,A_1165] :
      ( r2_hidden(B_1164,A_1165)
      | r1_tarski(A_1165,B_1164)
      | ~ r2_hidden(A_1165,B_1164)
      | ~ v3_ordinal1(B_1164)
      | ~ v3_ordinal1(A_1165) ) ),
    inference(resolution,[status(thm)],[c_59721,c_513])).

tff(c_60261,plain,(
    ! [B_24,A_22] :
      ( r1_tarski(B_24,A_22)
      | B_24 = A_22
      | r2_hidden(A_22,B_24)
      | ~ v3_ordinal1(B_24)
      | ~ v3_ordinal1(A_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_60030])).

tff(c_60265,plain,(
    ! [B_1166,A_1167] :
      ( r1_tarski(B_1166,A_1167)
      | B_1166 = A_1167
      | r2_hidden(A_1167,B_1166)
      | ~ v3_ordinal1(B_1166)
      | ~ v3_ordinal1(A_1167) ) ),
    inference(resolution,[status(thm)],[c_32,c_60030])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60999,plain,(
    ! [B_1168,A_1169] :
      ( ~ r2_hidden(B_1168,A_1169)
      | r1_tarski(B_1168,A_1169)
      | B_1168 = A_1169
      | ~ v3_ordinal1(B_1168)
      | ~ v3_ordinal1(A_1169) ) ),
    inference(resolution,[status(thm)],[c_60265,c_2])).

tff(c_61330,plain,(
    ! [A_1170,B_1171] :
      ( r1_tarski(A_1170,B_1171)
      | r1_tarski(B_1171,A_1170)
      | B_1171 = A_1170
      | ~ v3_ordinal1(B_1171)
      | ~ v3_ordinal1(A_1170) ) ),
    inference(resolution,[status(thm)],[c_60261,c_60999])).

tff(c_40,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_61,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_51,c_40])).

tff(c_70,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_61])).

tff(c_61588,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61330,c_70])).

tff(c_61926,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_61588])).

tff(c_61928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_73,c_61926])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.13/21.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.13/21.79  
% 31.13/21.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.13/21.79  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 31.13/21.79  
% 31.13/21.79  %Foreground sorts:
% 31.13/21.79  
% 31.13/21.79  
% 31.13/21.79  %Background operators:
% 31.13/21.79  
% 31.13/21.79  
% 31.13/21.79  %Foreground operators:
% 31.13/21.79  tff('#skF_2', type, '#skF_2': $i > $i).
% 31.13/21.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.13/21.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.13/21.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 31.13/21.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 31.13/21.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.13/21.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.13/21.79  tff('#skF_3', type, '#skF_3': $i).
% 31.13/21.79  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 31.13/21.79  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 31.13/21.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.13/21.79  tff('#skF_4', type, '#skF_4': $i).
% 31.13/21.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.13/21.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 31.13/21.79  
% 31.13/21.80  tff(f_104, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 31.13/21.80  tff(f_44, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 31.13/21.80  tff(f_81, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 31.13/21.80  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 31.13/21.80  tff(f_66, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 31.13/21.80  tff(f_60, axiom, (![A]: (?[B]: (![C]: (r2_hidden(C, B) <=> (r2_hidden(C, A) & v3_ordinal1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 31.13/21.80  tff(f_88, axiom, (![A, B, C]: ~((r2_hidden(A, B) & r2_hidden(B, C)) & r2_hidden(C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_ordinal1)).
% 31.13/21.80  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 31.13/21.80  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 31.13/21.80  tff(c_51, plain, (![A_40, B_41]: (r2_xboole_0(A_40, B_41) | B_41=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_44])).
% 31.13/21.80  tff(c_36, plain, (~r2_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 31.13/21.80  tff(c_64, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_36])).
% 31.13/21.80  tff(c_73, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_64])).
% 31.13/21.80  tff(c_44, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 31.13/21.81  tff(c_42, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 31.13/21.81  tff(c_32, plain, (![B_24, A_22]: (r2_hidden(B_24, A_22) | B_24=A_22 | r2_hidden(A_22, B_24) | ~v3_ordinal1(B_24) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 31.13/21.81  tff(c_89, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.13/21.81  tff(c_30, plain, (![A_20, B_21]: (v3_ordinal1(A_20) | ~r2_hidden(A_20, B_21) | ~v3_ordinal1(B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 31.13/21.81  tff(c_109, plain, (![A_48, B_49]: (v3_ordinal1('#skF_1'(A_48, B_49)) | ~v3_ordinal1(A_48) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_89, c_30])).
% 31.13/21.81  tff(c_118, plain, (![C_56, A_57]: (r2_hidden(C_56, '#skF_2'(A_57)) | ~v3_ordinal1(C_56) | ~r2_hidden(C_56, A_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 31.13/21.81  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.13/21.81  tff(c_2376, plain, (![A_202, A_203]: (r1_tarski(A_202, '#skF_2'(A_203)) | ~v3_ordinal1('#skF_1'(A_202, '#skF_2'(A_203))) | ~r2_hidden('#skF_1'(A_202, '#skF_2'(A_203)), A_203))), inference(resolution, [status(thm)], [c_118, c_6])).
% 31.13/21.81  tff(c_22696, plain, (![A_685, B_686]: (r1_tarski(A_685, '#skF_2'(B_686)) | r2_hidden(B_686, '#skF_1'(A_685, '#skF_2'(B_686))) | '#skF_1'(A_685, '#skF_2'(B_686))=B_686 | ~v3_ordinal1(B_686) | ~v3_ordinal1('#skF_1'(A_685, '#skF_2'(B_686))))), inference(resolution, [status(thm)], [c_32, c_2376])).
% 31.13/21.81  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.13/21.81  tff(c_142, plain, (![C_58, A_59, B_60]: (~r2_hidden(C_58, A_59) | ~r2_hidden(B_60, C_58) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_88])).
% 31.13/21.81  tff(c_148, plain, (![B_60, A_3, B_4]: (~r2_hidden(B_60, '#skF_1'(A_3, B_4)) | ~r2_hidden(A_3, B_60) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_142])).
% 31.13/21.81  tff(c_42885, plain, (![A_973, B_974]: (~r2_hidden(A_973, B_974) | r1_tarski(A_973, '#skF_2'(B_974)) | '#skF_1'(A_973, '#skF_2'(B_974))=B_974 | ~v3_ordinal1(B_974) | ~v3_ordinal1('#skF_1'(A_973, '#skF_2'(B_974))))), inference(resolution, [status(thm)], [c_22696, c_148])).
% 31.13/21.81  tff(c_42904, plain, (![A_975, B_976]: (~r2_hidden(A_975, B_976) | '#skF_1'(A_975, '#skF_2'(B_976))=B_976 | ~v3_ordinal1(B_976) | ~v3_ordinal1(A_975) | r1_tarski(A_975, '#skF_2'(B_976)))), inference(resolution, [status(thm)], [c_109, c_42885])).
% 31.13/21.81  tff(c_113, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.13/21.81  tff(c_279, plain, (![A_74, B_75, B_76]: (r2_hidden('#skF_1'(A_74, B_75), B_76) | ~r1_tarski(A_74, B_76) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_8, c_113])).
% 31.13/21.81  tff(c_28, plain, (![C_19, A_14]: (r2_hidden(C_19, A_14) | ~r2_hidden(C_19, '#skF_2'(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 31.13/21.81  tff(c_466, plain, (![A_98, B_99, A_100]: (r2_hidden('#skF_1'(A_98, B_99), A_100) | ~r1_tarski(A_98, '#skF_2'(A_100)) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_279, c_28])).
% 31.13/21.81  tff(c_513, plain, (![A_98, A_100]: (~r1_tarski(A_98, '#skF_2'(A_100)) | r1_tarski(A_98, A_100))), inference(resolution, [status(thm)], [c_466, c_6])).
% 31.13/21.81  tff(c_43157, plain, (![A_977, B_978]: (r1_tarski(A_977, B_978) | ~r2_hidden(A_977, B_978) | '#skF_1'(A_977, '#skF_2'(B_978))=B_978 | ~v3_ordinal1(B_978) | ~v3_ordinal1(A_977))), inference(resolution, [status(thm)], [c_42904, c_513])).
% 31.13/21.81  tff(c_59721, plain, (![B_1162, A_1163]: (r2_hidden(B_1162, A_1163) | r1_tarski(A_1163, '#skF_2'(B_1162)) | r1_tarski(A_1163, B_1162) | ~r2_hidden(A_1163, B_1162) | ~v3_ordinal1(B_1162) | ~v3_ordinal1(A_1163))), inference(superposition, [status(thm), theory('equality')], [c_43157, c_8])).
% 31.13/21.81  tff(c_60030, plain, (![B_1164, A_1165]: (r2_hidden(B_1164, A_1165) | r1_tarski(A_1165, B_1164) | ~r2_hidden(A_1165, B_1164) | ~v3_ordinal1(B_1164) | ~v3_ordinal1(A_1165))), inference(resolution, [status(thm)], [c_59721, c_513])).
% 31.13/21.81  tff(c_60261, plain, (![B_24, A_22]: (r1_tarski(B_24, A_22) | B_24=A_22 | r2_hidden(A_22, B_24) | ~v3_ordinal1(B_24) | ~v3_ordinal1(A_22))), inference(resolution, [status(thm)], [c_32, c_60030])).
% 31.13/21.81  tff(c_60265, plain, (![B_1166, A_1167]: (r1_tarski(B_1166, A_1167) | B_1166=A_1167 | r2_hidden(A_1167, B_1166) | ~v3_ordinal1(B_1166) | ~v3_ordinal1(A_1167))), inference(resolution, [status(thm)], [c_32, c_60030])).
% 31.13/21.81  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 31.13/21.81  tff(c_60999, plain, (![B_1168, A_1169]: (~r2_hidden(B_1168, A_1169) | r1_tarski(B_1168, A_1169) | B_1168=A_1169 | ~v3_ordinal1(B_1168) | ~v3_ordinal1(A_1169))), inference(resolution, [status(thm)], [c_60265, c_2])).
% 31.13/21.81  tff(c_61330, plain, (![A_1170, B_1171]: (r1_tarski(A_1170, B_1171) | r1_tarski(B_1171, A_1170) | B_1171=A_1170 | ~v3_ordinal1(B_1171) | ~v3_ordinal1(A_1170))), inference(resolution, [status(thm)], [c_60261, c_60999])).
% 31.13/21.81  tff(c_40, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 31.13/21.81  tff(c_61, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_51, c_40])).
% 31.13/21.81  tff(c_70, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_61])).
% 31.13/21.81  tff(c_61588, plain, (r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_61330, c_70])).
% 31.13/21.81  tff(c_61926, plain, (r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_61588])).
% 31.13/21.81  tff(c_61928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_73, c_61926])).
% 31.13/21.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.13/21.81  
% 31.13/21.81  Inference rules
% 31.13/21.81  ----------------------
% 31.13/21.81  #Ref     : 0
% 31.13/21.81  #Sup     : 15842
% 31.13/21.81  #Fact    : 12
% 31.13/21.81  #Define  : 0
% 31.13/21.81  #Split   : 0
% 31.13/21.81  #Chain   : 0
% 31.13/21.81  #Close   : 0
% 31.13/21.81  
% 31.13/21.81  Ordering : KBO
% 31.13/21.81  
% 31.13/21.81  Simplification rules
% 31.13/21.81  ----------------------
% 31.13/21.81  #Subsume      : 3251
% 31.13/21.81  #Demod        : 453
% 31.13/21.81  #Tautology    : 600
% 31.13/21.81  #SimpNegUnit  : 3
% 31.13/21.81  #BackRed      : 0
% 31.13/21.81  
% 31.13/21.81  #Partial instantiations: 0
% 31.13/21.81  #Strategies tried      : 1
% 31.13/21.81  
% 31.13/21.81  Timing (in seconds)
% 31.13/21.81  ----------------------
% 31.13/21.81  Preprocessing        : 0.30
% 31.13/21.81  Parsing              : 0.16
% 31.13/21.81  CNF conversion       : 0.02
% 31.13/21.81  Main loop            : 20.74
% 31.13/21.81  Inferencing          : 1.55
% 31.13/21.81  Reduction            : 2.17
% 31.13/21.81  Demodulation         : 1.60
% 31.13/21.81  BG Simplification    : 0.27
% 31.13/21.81  Subsumption          : 15.89
% 31.13/21.81  Abstraction          : 0.38
% 31.13/21.81  MUC search           : 0.00
% 31.13/21.81  Cooper               : 0.00
% 31.13/21.81  Total                : 21.07
% 31.13/21.81  Index Insertion      : 0.00
% 31.13/21.81  Index Deletion       : 0.00
% 31.13/21.81  Index Matching       : 0.00
% 31.13/21.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
