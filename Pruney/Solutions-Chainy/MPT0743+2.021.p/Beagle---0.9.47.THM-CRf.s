%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:11 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 179 expanded)
%              Number of leaves         :   20 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 438 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_63,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_28,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( r2_hidden(B_14,A_12)
      | r1_ordinal1(A_12,B_14)
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_607,plain,(
    ! [B_107,A_108] :
      ( r2_hidden(B_107,A_108)
      | r1_ordinal1(A_108,B_107)
      | ~ v3_ordinal1(B_107)
      | ~ v3_ordinal1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_697,plain,(
    ! [A_115,B_116] :
      ( ~ r2_hidden(A_115,B_116)
      | r1_ordinal1(A_115,B_116)
      | ~ v3_ordinal1(B_116)
      | ~ v3_ordinal1(A_115) ) ),
    inference(resolution,[status(thm)],[c_607,c_2])).

tff(c_710,plain,(
    ! [B_14,A_12] :
      ( r1_ordinal1(B_14,A_12)
      | r1_ordinal1(A_12,B_14)
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_12) ) ),
    inference(resolution,[status(thm)],[c_20,c_697])).

tff(c_728,plain,(
    ! [B_14] :
      ( ~ v3_ordinal1(B_14)
      | r1_ordinal1(B_14,B_14) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_710])).

tff(c_22,plain,(
    ! [A_15] :
      ( v3_ordinal1(k1_ordinal1(A_15))
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_86,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_36])).

tff(c_148,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ r1_ordinal1(A_48,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden(A_28,B_29)
      | r2_hidden(A_28,k1_ordinal1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_73,plain,(
    ! [B_29,A_28] :
      ( ~ r1_tarski(k1_ordinal1(B_29),A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_61,c_24])).

tff(c_333,plain,(
    ! [B_73,B_74] :
      ( ~ r2_hidden(B_73,B_74)
      | ~ r1_ordinal1(k1_ordinal1(B_74),B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(k1_ordinal1(B_74)) ) ),
    inference(resolution,[status(thm)],[c_148,c_73])).

tff(c_360,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_86,c_333])).

tff(c_369,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_360])).

tff(c_370,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_373,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_370])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_373])).

tff(c_379,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_162,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | r1_ordinal1(A_51,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_200,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_162,c_60])).

tff(c_221,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_200])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_ordinal1(A_7,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_271,plain,(
    ! [A_61,B_62,A_63] :
      ( r1_tarski(A_61,B_62)
      | ~ r1_tarski(A_61,A_63)
      | ~ r1_ordinal1(A_63,B_62)
      | ~ v3_ordinal1(B_62)
      | ~ v3_ordinal1(A_63) ) ),
    inference(resolution,[status(thm)],[c_148,c_4])).

tff(c_443,plain,(
    ! [A_83,B_84,B_85] :
      ( r1_tarski(A_83,B_84)
      | ~ r1_ordinal1(B_85,B_84)
      | ~ v3_ordinal1(B_84)
      | ~ r1_ordinal1(A_83,B_85)
      | ~ v3_ordinal1(B_85)
      | ~ v3_ordinal1(A_83) ) ),
    inference(resolution,[status(thm)],[c_10,c_271])).

tff(c_463,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,'#skF_1')
      | ~ v3_ordinal1('#skF_1')
      | ~ r1_ordinal1(A_83,'#skF_2')
      | ~ v3_ordinal1('#skF_2')
      | ~ v3_ordinal1(A_83) ) ),
    inference(resolution,[status(thm)],[c_221,c_443])).

tff(c_483,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,'#skF_1')
      | ~ r1_ordinal1(A_86,'#skF_2')
      | ~ v3_ordinal1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_463])).

tff(c_16,plain,(
    ! [B_11] : r2_hidden(B_11,k1_ordinal1(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [B_21,A_22] :
      ( ~ r1_tarski(B_21,A_22)
      | ~ r2_hidden(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [B_11] : ~ r1_tarski(k1_ordinal1(B_11),B_11) ),
    inference(resolution,[status(thm)],[c_16,c_40])).

tff(c_498,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_483,c_44])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_86,c_498])).

tff(c_512,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_518,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_512,c_2])).

tff(c_730,plain,(
    ! [B_117,A_118] :
      ( r1_ordinal1(B_117,A_118)
      | r1_ordinal1(A_118,B_117)
      | ~ v3_ordinal1(B_117)
      | ~ v3_ordinal1(A_118) ) ),
    inference(resolution,[status(thm)],[c_20,c_697])).

tff(c_511,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_740,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_730,c_511])).

tff(c_757,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_740])).

tff(c_770,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_757])).

tff(c_773,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_770])).

tff(c_777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_773])).

tff(c_779,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_757])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | r2_hidden(A_10,B_11)
      | ~ r2_hidden(A_10,k1_ordinal1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_786,plain,(
    ! [B_124,B_123] :
      ( B_124 = B_123
      | r2_hidden(B_124,B_123)
      | r1_ordinal1(k1_ordinal1(B_123),B_124)
      | ~ v3_ordinal1(B_124)
      | ~ v3_ordinal1(k1_ordinal1(B_123)) ) ),
    inference(resolution,[status(thm)],[c_607,c_14])).

tff(c_793,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_786,c_511])).

tff(c_798,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_26,c_793])).

tff(c_799,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_798])).

tff(c_672,plain,(
    ! [A_112,B_113] :
      ( r1_tarski(A_112,B_113)
      | ~ r1_ordinal1(A_112,B_113)
      | ~ v3_ordinal1(B_113)
      | ~ v3_ordinal1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_519,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_512,c_24])).

tff(c_684,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_672,c_519])).

tff(c_694,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_684])).

tff(c_801,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_694])).

tff(c_815,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_728,c_801])).

tff(c_821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:03:31 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/2.35  
% 3.68/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/2.35  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 3.83/2.35  
% 3.83/2.35  %Foreground sorts:
% 3.83/2.35  
% 3.83/2.35  
% 3.83/2.35  %Background operators:
% 3.83/2.35  
% 3.83/2.35  
% 3.83/2.35  %Foreground operators:
% 3.83/2.35  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.83/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.83/2.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.83/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/2.35  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.83/2.35  tff('#skF_2', type, '#skF_2': $i).
% 3.83/2.35  tff('#skF_1', type, '#skF_1': $i).
% 3.83/2.35  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.83/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/2.35  
% 3.83/2.40  tff(f_82, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.83/2.40  tff(f_63, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.83/2.40  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.83/2.40  tff(f_67, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 3.83/2.40  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.83/2.40  tff(f_54, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.83/2.40  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.83/2.40  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.83/2.40  tff(c_28, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.83/2.40  tff(c_20, plain, (![B_14, A_12]: (r2_hidden(B_14, A_12) | r1_ordinal1(A_12, B_14) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.83/2.40  tff(c_607, plain, (![B_107, A_108]: (r2_hidden(B_107, A_108) | r1_ordinal1(A_108, B_107) | ~v3_ordinal1(B_107) | ~v3_ordinal1(A_108))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.83/2.40  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.83/2.40  tff(c_697, plain, (![A_115, B_116]: (~r2_hidden(A_115, B_116) | r1_ordinal1(A_115, B_116) | ~v3_ordinal1(B_116) | ~v3_ordinal1(A_115))), inference(resolution, [status(thm)], [c_607, c_2])).
% 3.83/2.40  tff(c_710, plain, (![B_14, A_12]: (r1_ordinal1(B_14, A_12) | r1_ordinal1(A_12, B_14) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_12))), inference(resolution, [status(thm)], [c_20, c_697])).
% 3.83/2.40  tff(c_728, plain, (![B_14]: (~v3_ordinal1(B_14) | r1_ordinal1(B_14, B_14))), inference(factorization, [status(thm), theory('equality')], [c_710])).
% 3.83/2.40  tff(c_22, plain, (![A_15]: (v3_ordinal1(k1_ordinal1(A_15)) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.83/2.40  tff(c_26, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.83/2.40  tff(c_30, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.83/2.40  tff(c_60, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 3.83/2.40  tff(c_36, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.83/2.40  tff(c_86, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_36])).
% 3.83/2.40  tff(c_148, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~r1_ordinal1(A_48, B_49) | ~v3_ordinal1(B_49) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.83/2.40  tff(c_61, plain, (![A_28, B_29]: (~r2_hidden(A_28, B_29) | r2_hidden(A_28, k1_ordinal1(B_29)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.83/2.40  tff(c_24, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.83/2.40  tff(c_73, plain, (![B_29, A_28]: (~r1_tarski(k1_ordinal1(B_29), A_28) | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_61, c_24])).
% 3.83/2.40  tff(c_333, plain, (![B_73, B_74]: (~r2_hidden(B_73, B_74) | ~r1_ordinal1(k1_ordinal1(B_74), B_73) | ~v3_ordinal1(B_73) | ~v3_ordinal1(k1_ordinal1(B_74)))), inference(resolution, [status(thm)], [c_148, c_73])).
% 3.83/2.40  tff(c_360, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_86, c_333])).
% 3.83/2.40  tff(c_369, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_360])).
% 3.83/2.40  tff(c_370, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_369])).
% 3.83/2.40  tff(c_373, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_370])).
% 3.83/2.40  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_373])).
% 3.83/2.40  tff(c_379, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_369])).
% 3.83/2.40  tff(c_162, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | r1_ordinal1(A_51, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.83/2.40  tff(c_200, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_162, c_60])).
% 3.83/2.40  tff(c_221, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_200])).
% 3.83/2.40  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~r1_ordinal1(A_7, B_8) | ~v3_ordinal1(B_8) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.83/2.40  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.83/2.40  tff(c_271, plain, (![A_61, B_62, A_63]: (r1_tarski(A_61, B_62) | ~r1_tarski(A_61, A_63) | ~r1_ordinal1(A_63, B_62) | ~v3_ordinal1(B_62) | ~v3_ordinal1(A_63))), inference(resolution, [status(thm)], [c_148, c_4])).
% 3.83/2.40  tff(c_443, plain, (![A_83, B_84, B_85]: (r1_tarski(A_83, B_84) | ~r1_ordinal1(B_85, B_84) | ~v3_ordinal1(B_84) | ~r1_ordinal1(A_83, B_85) | ~v3_ordinal1(B_85) | ~v3_ordinal1(A_83))), inference(resolution, [status(thm)], [c_10, c_271])).
% 3.83/2.40  tff(c_463, plain, (![A_83]: (r1_tarski(A_83, '#skF_1') | ~v3_ordinal1('#skF_1') | ~r1_ordinal1(A_83, '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(A_83))), inference(resolution, [status(thm)], [c_221, c_443])).
% 3.83/2.40  tff(c_483, plain, (![A_86]: (r1_tarski(A_86, '#skF_1') | ~r1_ordinal1(A_86, '#skF_2') | ~v3_ordinal1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_463])).
% 3.83/2.40  tff(c_16, plain, (![B_11]: (r2_hidden(B_11, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.83/2.40  tff(c_40, plain, (![B_21, A_22]: (~r1_tarski(B_21, A_22) | ~r2_hidden(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.83/2.40  tff(c_44, plain, (![B_11]: (~r1_tarski(k1_ordinal1(B_11), B_11))), inference(resolution, [status(thm)], [c_16, c_40])).
% 3.83/2.40  tff(c_498, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_483, c_44])).
% 3.83/2.40  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_379, c_86, c_498])).
% 3.83/2.40  tff(c_512, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 3.83/2.40  tff(c_518, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_512, c_2])).
% 3.83/2.40  tff(c_730, plain, (![B_117, A_118]: (r1_ordinal1(B_117, A_118) | r1_ordinal1(A_118, B_117) | ~v3_ordinal1(B_117) | ~v3_ordinal1(A_118))), inference(resolution, [status(thm)], [c_20, c_697])).
% 3.83/2.40  tff(c_511, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 3.83/2.40  tff(c_740, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_730, c_511])).
% 3.83/2.40  tff(c_757, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_740])).
% 3.83/2.40  tff(c_770, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_757])).
% 3.83/2.40  tff(c_773, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_770])).
% 3.83/2.40  tff(c_777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_773])).
% 3.83/2.40  tff(c_779, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_757])).
% 3.83/2.40  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | r2_hidden(A_10, B_11) | ~r2_hidden(A_10, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.83/2.40  tff(c_786, plain, (![B_124, B_123]: (B_124=B_123 | r2_hidden(B_124, B_123) | r1_ordinal1(k1_ordinal1(B_123), B_124) | ~v3_ordinal1(B_124) | ~v3_ordinal1(k1_ordinal1(B_123)))), inference(resolution, [status(thm)], [c_607, c_14])).
% 3.83/2.40  tff(c_793, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_786, c_511])).
% 3.83/2.40  tff(c_798, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_779, c_26, c_793])).
% 3.83/2.40  tff(c_799, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_518, c_798])).
% 3.83/2.40  tff(c_672, plain, (![A_112, B_113]: (r1_tarski(A_112, B_113) | ~r1_ordinal1(A_112, B_113) | ~v3_ordinal1(B_113) | ~v3_ordinal1(A_112))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.83/2.40  tff(c_519, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_512, c_24])).
% 3.83/2.40  tff(c_684, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_672, c_519])).
% 3.83/2.40  tff(c_694, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_684])).
% 3.83/2.40  tff(c_801, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_694])).
% 3.83/2.40  tff(c_815, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_728, c_801])).
% 3.83/2.40  tff(c_821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_815])).
% 3.83/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/2.40  
% 3.83/2.40  Inference rules
% 3.83/2.40  ----------------------
% 3.83/2.40  #Ref     : 0
% 3.83/2.40  #Sup     : 143
% 3.83/2.40  #Fact    : 4
% 3.83/2.40  #Define  : 0
% 3.83/2.40  #Split   : 4
% 3.83/2.40  #Chain   : 0
% 3.83/2.40  #Close   : 0
% 3.83/2.40  
% 3.83/2.40  Ordering : KBO
% 3.83/2.40  
% 3.83/2.40  Simplification rules
% 3.83/2.40  ----------------------
% 3.83/2.40  #Subsume      : 30
% 3.83/2.40  #Demod        : 48
% 3.83/2.40  #Tautology    : 22
% 3.83/2.40  #SimpNegUnit  : 2
% 3.83/2.40  #BackRed      : 8
% 3.83/2.40  
% 3.83/2.40  #Partial instantiations: 0
% 3.83/2.40  #Strategies tried      : 1
% 3.83/2.40  
% 3.83/2.40  Timing (in seconds)
% 3.83/2.40  ----------------------
% 3.83/2.40  Preprocessing        : 0.52
% 3.83/2.40  Parsing              : 0.31
% 3.83/2.40  CNF conversion       : 0.04
% 3.83/2.40  Main loop            : 0.90
% 3.83/2.40  Inferencing          : 0.36
% 3.83/2.40  Reduction            : 0.22
% 3.83/2.41  Demodulation         : 0.15
% 3.83/2.41  BG Simplification    : 0.05
% 3.83/2.41  Subsumption          : 0.24
% 3.83/2.41  Abstraction          : 0.04
% 3.83/2.41  MUC search           : 0.00
% 3.83/2.41  Cooper               : 0.00
% 3.83/2.41  Total                : 1.52
% 3.83/2.41  Index Insertion      : 0.00
% 3.83/2.41  Index Deletion       : 0.00
% 3.83/2.41  Index Matching       : 0.00
% 3.83/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
