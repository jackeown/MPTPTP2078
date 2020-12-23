%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:11 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 230 expanded)
%              Number of leaves         :   24 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  166 ( 577 expanded)
%              Number of equality atoms :   16 (  46 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_75,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_38,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [A_17] :
      ( v3_ordinal1(k1_ordinal1(A_17))
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_198,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,A_53)
      | r1_ordinal1(A_53,B_52)
      | ~ v3_ordinal1(B_52)
      | ~ v3_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_104,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42])).

tff(c_232,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_198,c_104])).

tff(c_246,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_232])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ r1_ordinal1(A_9,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_248,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ r1_ordinal1(A_54,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_361,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_ordinal1(A_70,B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v3_ordinal1(A_70) ) ),
    inference(resolution,[status(thm)],[c_248,c_2])).

tff(c_411,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_ordinal1(B_73,A_74)
      | ~ r1_ordinal1(A_74,B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_74) ) ),
    inference(resolution,[status(thm)],[c_22,c_361])).

tff(c_419,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_246,c_411])).

tff(c_428,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_419])).

tff(c_432,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_32,plain,(
    ! [B_16,A_14] :
      ( r2_hidden(B_16,A_14)
      | r1_ordinal1(A_14,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_421,plain,
    ( k1_ordinal1('#skF_2') = '#skF_3'
    | ~ r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_411])).

tff(c_431,plain,
    ( k1_ordinal1('#skF_2') = '#skF_3'
    | ~ r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_421])).

tff(c_433,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_436,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_433])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_436])).

tff(c_442,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_107,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden(A_35,B_36)
      | r2_hidden(A_35,k1_ordinal1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_111,plain,(
    ! [B_36,A_35] :
      ( ~ r1_tarski(k1_ordinal1(B_36),A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_107,c_36])).

tff(c_507,plain,(
    ! [B_79,B_80] :
      ( ~ r2_hidden(B_79,B_80)
      | ~ r1_ordinal1(k1_ordinal1(B_80),B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1(k1_ordinal1(B_80)) ) ),
    inference(resolution,[status(thm)],[c_248,c_111])).

tff(c_533,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_507])).

tff(c_542,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_38,c_533])).

tff(c_545,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_542])).

tff(c_548,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_545])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_548])).

tff(c_551,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_555,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_70])).

tff(c_28,plain,(
    ! [B_13] : r2_hidden(B_13,k1_ordinal1(B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_94,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_102,plain,(
    ! [B_13] : ~ r1_tarski(k1_ordinal1(B_13),B_13) ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_270,plain,(
    ! [B_55] :
      ( ~ r1_ordinal1(k1_ordinal1(B_55),B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(k1_ordinal1(B_55)) ) ),
    inference(resolution,[status(thm)],[c_248,c_102])).

tff(c_594,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_555,c_270])).

tff(c_600,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_594])).

tff(c_603,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_600])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_603])).

tff(c_608,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_634,plain,(
    ! [B_89,A_90] :
      ( ~ r1_tarski(B_89,A_90)
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_646,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_608,c_634])).

tff(c_61,plain,(
    ! [A_23] :
      ( v1_ordinal1(A_23)
      | ~ v3_ordinal1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_61])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_801,plain,(
    ! [B_117,A_118] :
      ( r2_hidden(B_117,A_118)
      | r1_ordinal1(A_118,B_117)
      | ~ v3_ordinal1(B_117)
      | ~ v3_ordinal1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | r2_hidden(A_12,B_13)
      | ~ r2_hidden(A_12,k1_ordinal1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_997,plain,(
    ! [B_135,B_134] :
      ( B_135 = B_134
      | r2_hidden(B_135,B_134)
      | r1_ordinal1(k1_ordinal1(B_134),B_135)
      | ~ v3_ordinal1(B_135)
      | ~ v3_ordinal1(k1_ordinal1(B_134)) ) ),
    inference(resolution,[status(thm)],[c_801,c_26])).

tff(c_609,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1007,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_997,c_609])).

tff(c_1013,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1007])).

tff(c_1014,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1013])).

tff(c_1017,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1014])).

tff(c_1021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1017])).

tff(c_1022,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1013])).

tff(c_1032,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1022])).

tff(c_1037,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_646])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1037])).

tff(c_1047,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1022])).

tff(c_14,plain,(
    ! [B_8,A_5] :
      ( r1_tarski(B_8,A_5)
      | ~ r2_hidden(B_8,A_5)
      | ~ v1_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1051,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1047,c_14])).

tff(c_1057,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1051])).

tff(c_1059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_1057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:28:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.43  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3
% 2.73/1.43  
% 2.73/1.43  %Foreground sorts:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Background operators:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Foreground operators:
% 2.73/1.43  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.43  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.73/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.43  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.73/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.43  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.73/1.43  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.43  
% 3.07/1.45  tff(f_90, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.07/1.45  tff(f_75, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 3.07/1.45  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.07/1.45  tff(f_54, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.07/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.07/1.45  tff(f_62, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.07/1.45  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.07/1.45  tff(f_37, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 3.07/1.45  tff(f_46, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 3.07/1.45  tff(c_38, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.07/1.45  tff(c_34, plain, (![A_17]: (v3_ordinal1(k1_ordinal1(A_17)) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.07/1.45  tff(c_40, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.07/1.45  tff(c_198, plain, (![B_52, A_53]: (r2_hidden(B_52, A_53) | r1_ordinal1(A_53, B_52) | ~v3_ordinal1(B_52) | ~v3_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.45  tff(c_48, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.07/1.45  tff(c_70, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 3.07/1.45  tff(c_42, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.07/1.45  tff(c_104, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42])).
% 3.07/1.45  tff(c_232, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_198, c_104])).
% 3.07/1.45  tff(c_246, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_232])).
% 3.07/1.45  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~r1_ordinal1(A_9, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.07/1.45  tff(c_248, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~r1_ordinal1(A_54, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_54))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.07/1.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.45  tff(c_361, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_ordinal1(A_70, B_69) | ~v3_ordinal1(B_69) | ~v3_ordinal1(A_70))), inference(resolution, [status(thm)], [c_248, c_2])).
% 3.07/1.45  tff(c_411, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_ordinal1(B_73, A_74) | ~r1_ordinal1(A_74, B_73) | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_74))), inference(resolution, [status(thm)], [c_22, c_361])).
% 3.07/1.45  tff(c_419, plain, ('#skF_2'='#skF_3' | ~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_246, c_411])).
% 3.07/1.45  tff(c_428, plain, ('#skF_2'='#skF_3' | ~r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_419])).
% 3.07/1.45  tff(c_432, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_428])).
% 3.07/1.45  tff(c_32, plain, (![B_16, A_14]: (r2_hidden(B_16, A_14) | r1_ordinal1(A_14, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.45  tff(c_421, plain, (k1_ordinal1('#skF_2')='#skF_3' | ~r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_411])).
% 3.07/1.45  tff(c_431, plain, (k1_ordinal1('#skF_2')='#skF_3' | ~r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_421])).
% 3.07/1.45  tff(c_433, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_431])).
% 3.07/1.45  tff(c_436, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_433])).
% 3.07/1.45  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_436])).
% 3.07/1.45  tff(c_442, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_431])).
% 3.07/1.45  tff(c_107, plain, (![A_35, B_36]: (~r2_hidden(A_35, B_36) | r2_hidden(A_35, k1_ordinal1(B_36)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.07/1.45  tff(c_36, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.07/1.45  tff(c_111, plain, (![B_36, A_35]: (~r1_tarski(k1_ordinal1(B_36), A_35) | ~r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_107, c_36])).
% 3.07/1.45  tff(c_507, plain, (![B_79, B_80]: (~r2_hidden(B_79, B_80) | ~r1_ordinal1(k1_ordinal1(B_80), B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1(k1_ordinal1(B_80)))), inference(resolution, [status(thm)], [c_248, c_111])).
% 3.07/1.45  tff(c_533, plain, (~r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_70, c_507])).
% 3.07/1.45  tff(c_542, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_38, c_533])).
% 3.07/1.45  tff(c_545, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_542])).
% 3.07/1.45  tff(c_548, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_545])).
% 3.07/1.45  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_432, c_548])).
% 3.07/1.45  tff(c_551, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_428])).
% 3.07/1.45  tff(c_555, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_551, c_70])).
% 3.07/1.45  tff(c_28, plain, (![B_13]: (r2_hidden(B_13, k1_ordinal1(B_13)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.07/1.45  tff(c_94, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.07/1.45  tff(c_102, plain, (![B_13]: (~r1_tarski(k1_ordinal1(B_13), B_13))), inference(resolution, [status(thm)], [c_28, c_94])).
% 3.07/1.45  tff(c_270, plain, (![B_55]: (~r1_ordinal1(k1_ordinal1(B_55), B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(k1_ordinal1(B_55)))), inference(resolution, [status(thm)], [c_248, c_102])).
% 3.07/1.45  tff(c_594, plain, (~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_555, c_270])).
% 3.07/1.45  tff(c_600, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_594])).
% 3.07/1.45  tff(c_603, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_600])).
% 3.07/1.45  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_603])).
% 3.07/1.45  tff(c_608, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 3.07/1.45  tff(c_634, plain, (![B_89, A_90]: (~r1_tarski(B_89, A_90) | ~r2_hidden(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.07/1.45  tff(c_646, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_608, c_634])).
% 3.07/1.45  tff(c_61, plain, (![A_23]: (v1_ordinal1(A_23) | ~v3_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.45  tff(c_69, plain, (v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_61])).
% 3.07/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.45  tff(c_801, plain, (![B_117, A_118]: (r2_hidden(B_117, A_118) | r1_ordinal1(A_118, B_117) | ~v3_ordinal1(B_117) | ~v3_ordinal1(A_118))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.45  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | r2_hidden(A_12, B_13) | ~r2_hidden(A_12, k1_ordinal1(B_13)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.07/1.45  tff(c_997, plain, (![B_135, B_134]: (B_135=B_134 | r2_hidden(B_135, B_134) | r1_ordinal1(k1_ordinal1(B_134), B_135) | ~v3_ordinal1(B_135) | ~v3_ordinal1(k1_ordinal1(B_134)))), inference(resolution, [status(thm)], [c_801, c_26])).
% 3.07/1.45  tff(c_609, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 3.07/1.45  tff(c_1007, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_997, c_609])).
% 3.07/1.45  tff(c_1013, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1007])).
% 3.07/1.45  tff(c_1014, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1013])).
% 3.07/1.45  tff(c_1017, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1014])).
% 3.07/1.45  tff(c_1021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1017])).
% 3.07/1.45  tff(c_1022, plain, (r2_hidden('#skF_3', '#skF_2') | '#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1013])).
% 3.07/1.45  tff(c_1032, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_1022])).
% 3.07/1.45  tff(c_1037, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_646])).
% 3.07/1.45  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1037])).
% 3.07/1.45  tff(c_1047, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1022])).
% 3.07/1.45  tff(c_14, plain, (![B_8, A_5]: (r1_tarski(B_8, A_5) | ~r2_hidden(B_8, A_5) | ~v1_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.45  tff(c_1051, plain, (r1_tarski('#skF_3', '#skF_2') | ~v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_1047, c_14])).
% 3.07/1.45  tff(c_1057, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1051])).
% 3.07/1.45  tff(c_1059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_1057])).
% 3.07/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.45  
% 3.07/1.45  Inference rules
% 3.07/1.45  ----------------------
% 3.07/1.45  #Ref     : 0
% 3.07/1.45  #Sup     : 188
% 3.07/1.45  #Fact    : 2
% 3.07/1.45  #Define  : 0
% 3.07/1.45  #Split   : 6
% 3.07/1.45  #Chain   : 0
% 3.07/1.45  #Close   : 0
% 3.07/1.45  
% 3.07/1.45  Ordering : KBO
% 3.07/1.45  
% 3.07/1.45  Simplification rules
% 3.07/1.45  ----------------------
% 3.07/1.45  #Subsume      : 41
% 3.07/1.45  #Demod        : 68
% 3.07/1.45  #Tautology    : 44
% 3.07/1.45  #SimpNegUnit  : 2
% 3.07/1.45  #BackRed      : 16
% 3.07/1.45  
% 3.07/1.45  #Partial instantiations: 0
% 3.07/1.45  #Strategies tried      : 1
% 3.07/1.45  
% 3.07/1.45  Timing (in seconds)
% 3.07/1.45  ----------------------
% 3.07/1.46  Preprocessing        : 0.28
% 3.07/1.46  Parsing              : 0.16
% 3.07/1.46  CNF conversion       : 0.02
% 3.07/1.46  Main loop            : 0.40
% 3.07/1.46  Inferencing          : 0.16
% 3.07/1.46  Reduction            : 0.11
% 3.07/1.46  Demodulation         : 0.07
% 3.07/1.46  BG Simplification    : 0.02
% 3.07/1.46  Subsumption          : 0.08
% 3.07/1.46  Abstraction          : 0.02
% 3.07/1.46  MUC search           : 0.00
% 3.07/1.46  Cooper               : 0.00
% 3.07/1.46  Total                : 0.72
% 3.07/1.46  Index Insertion      : 0.00
% 3.07/1.46  Index Deletion       : 0.00
% 3.07/1.46  Index Matching       : 0.00
% 3.07/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
