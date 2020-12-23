%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:10 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 186 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 446 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_72,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_68,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    ! [A_17] :
      ( v3_ordinal1(k1_ordinal1(A_17))
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_64,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_247,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | ~ r1_ordinal1(A_65,B_66)
      | ~ v3_ordinal1(B_66)
      | ~ v3_ordinal1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden(A_35,B_36)
      | r2_hidden(A_35,k1_ordinal1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,(
    ! [B_36,A_35] :
      ( ~ r1_tarski(k1_ordinal1(B_36),A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_84,c_32])).

tff(c_526,plain,(
    ! [B_97,B_98] :
      ( ~ r2_hidden(B_97,B_98)
      | ~ r1_ordinal1(k1_ordinal1(B_98),B_97)
      | ~ v3_ordinal1(B_97)
      | ~ v3_ordinal1(k1_ordinal1(B_98)) ) ),
    inference(resolution,[status(thm)],[c_247,c_94])).

tff(c_560,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_526])).

tff(c_571,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_560])).

tff(c_572,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_575,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_572])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_575])).

tff(c_581,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_28,plain,(
    ! [B_16,A_14] :
      ( r2_hidden(B_16,A_14)
      | r1_ordinal1(A_14,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_580,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_584,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_580])).

tff(c_587,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_584])).

tff(c_266,plain,(
    ! [B_67,A_68] :
      ( r2_hidden(B_67,A_68)
      | r1_ordinal1(A_68,B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_111,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_38])).

tff(c_312,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_266,c_111])).

tff(c_343,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_312])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ r1_ordinal1(A_9,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_494,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(B_91,A_92)
      | ~ r1_ordinal1(A_92,B_91)
      | ~ v3_ordinal1(B_91)
      | ~ v3_ordinal1(A_92) ) ),
    inference(resolution,[status(thm)],[c_247,c_4])).

tff(c_588,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_ordinal1(B_99,A_100)
      | ~ r1_ordinal1(A_100,B_99)
      | ~ v3_ordinal1(B_99)
      | ~ v3_ordinal1(A_100) ) ),
    inference(resolution,[status(thm)],[c_18,c_494])).

tff(c_608,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_343,c_588])).

tff(c_626,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_587,c_608])).

tff(c_634,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_64])).

tff(c_22,plain,(
    ! [B_12] : r2_hidden(B_12,k1_ordinal1(B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_70,plain,(
    ! [B_12] : ~ r1_tarski(k1_ordinal1(B_12),B_12) ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_265,plain,(
    ! [B_66] :
      ( ~ r1_ordinal1(k1_ordinal1(B_66),B_66)
      | ~ v3_ordinal1(B_66)
      | ~ v3_ordinal1(k1_ordinal1(B_66)) ) ),
    inference(resolution,[status(thm)],[c_247,c_70])).

tff(c_683,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_634,c_265])).

tff(c_694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_36,c_683])).

tff(c_695,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_699,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_695,c_2])).

tff(c_870,plain,(
    ! [B_135,A_136] :
      ( r2_hidden(B_135,A_136)
      | r1_ordinal1(A_136,B_135)
      | ~ v3_ordinal1(B_135)
      | ~ v3_ordinal1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1014,plain,(
    ! [A_147,B_148] :
      ( ~ r2_hidden(A_147,B_148)
      | r1_ordinal1(A_147,B_148)
      | ~ v3_ordinal1(B_148)
      | ~ v3_ordinal1(A_147) ) ),
    inference(resolution,[status(thm)],[c_870,c_2])).

tff(c_1047,plain,(
    ! [B_149,A_150] :
      ( r1_ordinal1(B_149,A_150)
      | r1_ordinal1(A_150,B_149)
      | ~ v3_ordinal1(B_149)
      | ~ v3_ordinal1(A_150) ) ),
    inference(resolution,[status(thm)],[c_28,c_1014])).

tff(c_696,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1057,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1047,c_696])).

tff(c_1074,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1057])).

tff(c_1082,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1074])).

tff(c_1086,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1082])).

tff(c_1090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1086])).

tff(c_1092,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1074])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | r2_hidden(A_11,B_12)
      | ~ r2_hidden(A_11,k1_ordinal1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1243,plain,(
    ! [B_171,B_170] :
      ( B_171 = B_170
      | r2_hidden(B_170,B_171)
      | r1_ordinal1(k1_ordinal1(B_171),B_170)
      | ~ v3_ordinal1(B_170)
      | ~ v3_ordinal1(k1_ordinal1(B_171)) ) ),
    inference(resolution,[status(thm)],[c_870,c_20])).

tff(c_1253,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1243,c_696])).

tff(c_1259,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_34,c_1253])).

tff(c_1260,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_1259])).

tff(c_701,plain,(
    ! [B_104,A_105] :
      ( ~ r1_tarski(B_104,A_105)
      | ~ r2_hidden(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_708,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_695,c_701])).

tff(c_1264,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_708])).

tff(c_1271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:12:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.61  
% 3.44/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.62  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 3.44/1.62  
% 3.44/1.62  %Foreground sorts:
% 3.44/1.62  
% 3.44/1.62  
% 3.44/1.62  %Background operators:
% 3.44/1.62  
% 3.44/1.62  
% 3.44/1.62  %Foreground operators:
% 3.44/1.62  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.44/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.62  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.44/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.62  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.44/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.62  
% 3.44/1.63  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.63  tff(f_87, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.44/1.63  tff(f_72, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 3.44/1.63  tff(f_50, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.44/1.63  tff(f_56, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.44/1.63  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.44/1.63  tff(f_68, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.44/1.63  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.44/1.63  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.63  tff(c_36, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.44/1.63  tff(c_30, plain, (![A_17]: (v3_ordinal1(k1_ordinal1(A_17)) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.44/1.63  tff(c_34, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.44/1.63  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.44/1.63  tff(c_64, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 3.44/1.63  tff(c_247, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | ~r1_ordinal1(A_65, B_66) | ~v3_ordinal1(B_66) | ~v3_ordinal1(A_65))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.63  tff(c_84, plain, (![A_35, B_36]: (~r2_hidden(A_35, B_36) | r2_hidden(A_35, k1_ordinal1(B_36)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.63  tff(c_32, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.63  tff(c_94, plain, (![B_36, A_35]: (~r1_tarski(k1_ordinal1(B_36), A_35) | ~r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_84, c_32])).
% 3.44/1.63  tff(c_526, plain, (![B_97, B_98]: (~r2_hidden(B_97, B_98) | ~r1_ordinal1(k1_ordinal1(B_98), B_97) | ~v3_ordinal1(B_97) | ~v3_ordinal1(k1_ordinal1(B_98)))), inference(resolution, [status(thm)], [c_247, c_94])).
% 3.44/1.63  tff(c_560, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_526])).
% 3.44/1.63  tff(c_571, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_560])).
% 3.44/1.63  tff(c_572, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_571])).
% 3.44/1.63  tff(c_575, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_572])).
% 3.44/1.63  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_575])).
% 3.44/1.63  tff(c_581, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_571])).
% 3.44/1.63  tff(c_28, plain, (![B_16, A_14]: (r2_hidden(B_16, A_14) | r1_ordinal1(A_14, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.63  tff(c_580, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_571])).
% 3.44/1.63  tff(c_584, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_580])).
% 3.44/1.63  tff(c_587, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_584])).
% 3.44/1.63  tff(c_266, plain, (![B_67, A_68]: (r2_hidden(B_67, A_68) | r1_ordinal1(A_68, B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1(A_68))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.63  tff(c_38, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.44/1.63  tff(c_111, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_38])).
% 3.44/1.63  tff(c_312, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_266, c_111])).
% 3.44/1.63  tff(c_343, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_312])).
% 3.44/1.63  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~r1_ordinal1(A_9, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.63  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.63  tff(c_494, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(B_91, A_92) | ~r1_ordinal1(A_92, B_91) | ~v3_ordinal1(B_91) | ~v3_ordinal1(A_92))), inference(resolution, [status(thm)], [c_247, c_4])).
% 3.44/1.63  tff(c_588, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_ordinal1(B_99, A_100) | ~r1_ordinal1(A_100, B_99) | ~v3_ordinal1(B_99) | ~v3_ordinal1(A_100))), inference(resolution, [status(thm)], [c_18, c_494])).
% 3.44/1.63  tff(c_608, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_343, c_588])).
% 3.44/1.63  tff(c_626, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_587, c_608])).
% 3.44/1.63  tff(c_634, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_626, c_64])).
% 3.44/1.63  tff(c_22, plain, (![B_12]: (r2_hidden(B_12, k1_ordinal1(B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.63  tff(c_66, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.63  tff(c_70, plain, (![B_12]: (~r1_tarski(k1_ordinal1(B_12), B_12))), inference(resolution, [status(thm)], [c_22, c_66])).
% 3.44/1.63  tff(c_265, plain, (![B_66]: (~r1_ordinal1(k1_ordinal1(B_66), B_66) | ~v3_ordinal1(B_66) | ~v3_ordinal1(k1_ordinal1(B_66)))), inference(resolution, [status(thm)], [c_247, c_70])).
% 3.44/1.63  tff(c_683, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_634, c_265])).
% 3.44/1.63  tff(c_694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_581, c_36, c_683])).
% 3.44/1.63  tff(c_695, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 3.44/1.63  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.44/1.63  tff(c_699, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_695, c_2])).
% 3.44/1.63  tff(c_870, plain, (![B_135, A_136]: (r2_hidden(B_135, A_136) | r1_ordinal1(A_136, B_135) | ~v3_ordinal1(B_135) | ~v3_ordinal1(A_136))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.63  tff(c_1014, plain, (![A_147, B_148]: (~r2_hidden(A_147, B_148) | r1_ordinal1(A_147, B_148) | ~v3_ordinal1(B_148) | ~v3_ordinal1(A_147))), inference(resolution, [status(thm)], [c_870, c_2])).
% 3.44/1.63  tff(c_1047, plain, (![B_149, A_150]: (r1_ordinal1(B_149, A_150) | r1_ordinal1(A_150, B_149) | ~v3_ordinal1(B_149) | ~v3_ordinal1(A_150))), inference(resolution, [status(thm)], [c_28, c_1014])).
% 3.44/1.63  tff(c_696, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 3.44/1.63  tff(c_1057, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_1047, c_696])).
% 3.44/1.63  tff(c_1074, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1057])).
% 3.44/1.63  tff(c_1082, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1074])).
% 3.44/1.63  tff(c_1086, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1082])).
% 3.44/1.63  tff(c_1090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1086])).
% 3.44/1.63  tff(c_1092, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_1074])).
% 3.44/1.63  tff(c_20, plain, (![B_12, A_11]: (B_12=A_11 | r2_hidden(A_11, B_12) | ~r2_hidden(A_11, k1_ordinal1(B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.63  tff(c_1243, plain, (![B_171, B_170]: (B_171=B_170 | r2_hidden(B_170, B_171) | r1_ordinal1(k1_ordinal1(B_171), B_170) | ~v3_ordinal1(B_170) | ~v3_ordinal1(k1_ordinal1(B_171)))), inference(resolution, [status(thm)], [c_870, c_20])).
% 3.44/1.63  tff(c_1253, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_1243, c_696])).
% 3.44/1.63  tff(c_1259, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_34, c_1253])).
% 3.44/1.63  tff(c_1260, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_699, c_1259])).
% 3.44/1.63  tff(c_701, plain, (![B_104, A_105]: (~r1_tarski(B_104, A_105) | ~r2_hidden(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.63  tff(c_708, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_695, c_701])).
% 3.44/1.63  tff(c_1264, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_708])).
% 3.44/1.63  tff(c_1271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1264])).
% 3.44/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.63  
% 3.44/1.63  Inference rules
% 3.44/1.63  ----------------------
% 3.44/1.63  #Ref     : 0
% 3.44/1.63  #Sup     : 230
% 3.44/1.63  #Fact    : 4
% 3.44/1.63  #Define  : 0
% 3.44/1.63  #Split   : 4
% 3.44/1.63  #Chain   : 0
% 3.44/1.63  #Close   : 0
% 3.44/1.63  
% 3.44/1.63  Ordering : KBO
% 3.44/1.63  
% 3.44/1.63  Simplification rules
% 3.44/1.63  ----------------------
% 3.44/1.63  #Subsume      : 73
% 3.44/1.63  #Demod        : 73
% 3.44/1.63  #Tautology    : 37
% 3.44/1.63  #SimpNegUnit  : 10
% 3.44/1.63  #BackRed      : 14
% 3.44/1.63  
% 3.44/1.63  #Partial instantiations: 0
% 3.44/1.63  #Strategies tried      : 1
% 3.44/1.63  
% 3.44/1.63  Timing (in seconds)
% 3.44/1.63  ----------------------
% 3.44/1.64  Preprocessing        : 0.33
% 3.44/1.64  Parsing              : 0.16
% 3.44/1.64  CNF conversion       : 0.02
% 3.44/1.64  Main loop            : 0.53
% 3.44/1.64  Inferencing          : 0.21
% 3.44/1.64  Reduction            : 0.14
% 3.44/1.64  Demodulation         : 0.10
% 3.44/1.64  BG Simplification    : 0.02
% 3.44/1.64  Subsumption          : 0.12
% 3.44/1.64  Abstraction          : 0.03
% 3.44/1.64  MUC search           : 0.00
% 3.44/1.64  Cooper               : 0.00
% 3.44/1.64  Total                : 0.90
% 3.44/1.64  Index Insertion      : 0.00
% 3.44/1.64  Index Deletion       : 0.00
% 3.44/1.64  Index Matching       : 0.00
% 3.44/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
