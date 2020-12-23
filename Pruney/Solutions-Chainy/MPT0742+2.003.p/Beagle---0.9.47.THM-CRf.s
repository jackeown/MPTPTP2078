%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:07 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   72 (  93 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 202 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ~ ( r1_tarski(A,B)
            & A != k1_xboole_0
            & ! [C] :
                ( v3_ordinal1(C)
               => ~ ( r2_hidden(C,A)
                    & ! [D] :
                        ( v3_ordinal1(D)
                       => ( r2_hidden(D,A)
                         => r1_ordinal1(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_42,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [A_60] : r1_tarski(A_60,A_60) ),
    inference(resolution,[status(thm)],[c_96,c_4])).

tff(c_38,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_2'(A_28,B_29),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_134,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_272,plain,(
    ! [A_91,B_92,B_93] :
      ( r2_hidden('#skF_2'(A_91,B_92),B_93)
      | ~ r1_tarski(B_92,B_93)
      | ~ r2_hidden(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_434,plain,(
    ! [A_138,B_139,B_140,B_141] :
      ( r2_hidden('#skF_2'(A_138,B_139),B_140)
      | ~ r1_tarski(B_141,B_140)
      | ~ r1_tarski(B_139,B_141)
      | ~ r2_hidden(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_272,c_2])).

tff(c_441,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_2'(A_142,B_143),'#skF_4')
      | ~ r1_tarski(B_143,'#skF_3')
      | ~ r2_hidden(A_142,B_143) ) ),
    inference(resolution,[status(thm)],[c_36,c_434])).

tff(c_30,plain,(
    ! [A_35,B_36] :
      ( v3_ordinal1(A_35)
      | ~ r2_hidden(A_35,B_36)
      | ~ v3_ordinal1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_446,plain,(
    ! [A_142,B_143] :
      ( v3_ordinal1('#skF_2'(A_142,B_143))
      | ~ v3_ordinal1('#skF_4')
      | ~ r1_tarski(B_143,'#skF_3')
      | ~ r2_hidden(A_142,B_143) ) ),
    inference(resolution,[status(thm)],[c_441,c_30])).

tff(c_450,plain,(
    ! [A_142,B_143] :
      ( v3_ordinal1('#skF_2'(A_142,B_143))
      | ~ r1_tarski(B_143,'#skF_3')
      | ~ r2_hidden(A_142,B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_446])).

tff(c_143,plain,(
    ! [A_28,B_29,B_69] :
      ( r2_hidden('#skF_2'(A_28,B_29),B_69)
      | ~ r1_tarski(B_29,B_69)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_44,plain,(
    ! [C_43] :
      ( v3_ordinal1('#skF_5'(C_43))
      | ~ r2_hidden(C_43,'#skF_3')
      | ~ v3_ordinal1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    ! [C_43] :
      ( r2_hidden('#skF_5'(C_43),'#skF_3')
      | ~ r2_hidden(C_43,'#skF_3')
      | ~ v3_ordinal1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    ! [B_39,A_37] :
      ( r2_hidden(B_39,A_37)
      | r1_ordinal1(A_37,B_39)
      | ~ v3_ordinal1(B_39)
      | ~ v3_ordinal1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_243,plain,(
    ! [D_86,A_87,B_88] :
      ( ~ r2_hidden(D_86,'#skF_2'(A_87,B_88))
      | ~ r2_hidden(D_86,B_88)
      | ~ r2_hidden(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_618,plain,(
    ! [B_171,B_172,A_173] :
      ( ~ r2_hidden(B_171,B_172)
      | ~ r2_hidden(A_173,B_172)
      | r1_ordinal1('#skF_2'(A_173,B_172),B_171)
      | ~ v3_ordinal1(B_171)
      | ~ v3_ordinal1('#skF_2'(A_173,B_172)) ) ),
    inference(resolution,[status(thm)],[c_32,c_243])).

tff(c_40,plain,(
    ! [C_43] :
      ( ~ r1_ordinal1(C_43,'#skF_5'(C_43))
      | ~ r2_hidden(C_43,'#skF_3')
      | ~ v3_ordinal1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_635,plain,(
    ! [A_184,B_185] :
      ( ~ r2_hidden('#skF_2'(A_184,B_185),'#skF_3')
      | ~ r2_hidden('#skF_5'('#skF_2'(A_184,B_185)),B_185)
      | ~ r2_hidden(A_184,B_185)
      | ~ v3_ordinal1('#skF_5'('#skF_2'(A_184,B_185)))
      | ~ v3_ordinal1('#skF_2'(A_184,B_185)) ) ),
    inference(resolution,[status(thm)],[c_618,c_40])).

tff(c_802,plain,(
    ! [A_214] :
      ( ~ r2_hidden(A_214,'#skF_3')
      | ~ v3_ordinal1('#skF_5'('#skF_2'(A_214,'#skF_3')))
      | ~ r2_hidden('#skF_2'(A_214,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_214,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_635])).

tff(c_807,plain,(
    ! [A_215] :
      ( ~ r2_hidden(A_215,'#skF_3')
      | ~ r2_hidden('#skF_2'(A_215,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_215,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_802])).

tff(c_815,plain,(
    ! [A_28] :
      ( ~ v3_ordinal1('#skF_2'(A_28,'#skF_3'))
      | ~ r1_tarski('#skF_3','#skF_3')
      | ~ r2_hidden(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_807])).

tff(c_831,plain,(
    ! [A_216] :
      ( ~ v3_ordinal1('#skF_2'(A_216,'#skF_3'))
      | ~ r2_hidden(A_216,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_815])).

tff(c_835,plain,(
    ! [A_142] :
      ( ~ r1_tarski('#skF_3','#skF_3')
      | ~ r2_hidden(A_142,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_450,c_831])).

tff(c_849,plain,(
    ! [A_217] : ~ r2_hidden(A_217,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_835])).

tff(c_887,plain,(
    ! [B_218] : r1_tarski('#skF_3',B_218) ),
    inference(resolution,[status(thm)],[c_6,c_849])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_949,plain,(
    ! [B_219] : k2_xboole_0('#skF_3',B_219) = B_219 ),
    inference(resolution,[status(thm)],[c_887,c_8])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_160,plain,(
    ! [A_78,B_79] : k5_xboole_0(k5_xboole_0(A_78,B_79),k2_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181,plain,(
    ! [A_9] : k5_xboole_0(A_9,k2_xboole_0(A_9,k1_xboole_0)) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_160])).

tff(c_184,plain,(
    ! [A_9] : k5_xboole_0(A_9,k2_xboole_0(A_9,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_181])).

tff(c_967,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_184])).

tff(c_986,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_967])).

tff(c_988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:02:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.56  
% 3.38/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.56  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.38/1.56  
% 3.38/1.56  %Foreground sorts:
% 3.38/1.56  
% 3.38/1.56  
% 3.38/1.56  %Background operators:
% 3.38/1.56  
% 3.38/1.56  
% 3.38/1.56  %Foreground operators:
% 3.38/1.56  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.38/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.56  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.38/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.56  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.38/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.38/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.56  
% 3.38/1.58  tff(f_102, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_ordinal1)).
% 3.38/1.58  tff(f_40, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.38/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.38/1.58  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 3.38/1.58  tff(f_71, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 3.38/1.58  tff(f_80, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.38/1.58  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.38/1.58  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.38/1.58  tff(f_42, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.38/1.58  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.38/1.58  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.38/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.58  tff(c_96, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.58  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.58  tff(c_104, plain, (![A_60]: (r1_tarski(A_60, A_60))), inference(resolution, [status(thm)], [c_96, c_4])).
% 3.38/1.58  tff(c_38, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.38/1.58  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.38/1.58  tff(c_28, plain, (![A_28, B_29]: (r2_hidden('#skF_2'(A_28, B_29), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.58  tff(c_134, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.58  tff(c_272, plain, (![A_91, B_92, B_93]: (r2_hidden('#skF_2'(A_91, B_92), B_93) | ~r1_tarski(B_92, B_93) | ~r2_hidden(A_91, B_92))), inference(resolution, [status(thm)], [c_28, c_134])).
% 3.38/1.58  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.58  tff(c_434, plain, (![A_138, B_139, B_140, B_141]: (r2_hidden('#skF_2'(A_138, B_139), B_140) | ~r1_tarski(B_141, B_140) | ~r1_tarski(B_139, B_141) | ~r2_hidden(A_138, B_139))), inference(resolution, [status(thm)], [c_272, c_2])).
% 3.38/1.58  tff(c_441, plain, (![A_142, B_143]: (r2_hidden('#skF_2'(A_142, B_143), '#skF_4') | ~r1_tarski(B_143, '#skF_3') | ~r2_hidden(A_142, B_143))), inference(resolution, [status(thm)], [c_36, c_434])).
% 3.38/1.58  tff(c_30, plain, (![A_35, B_36]: (v3_ordinal1(A_35) | ~r2_hidden(A_35, B_36) | ~v3_ordinal1(B_36))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.38/1.58  tff(c_446, plain, (![A_142, B_143]: (v3_ordinal1('#skF_2'(A_142, B_143)) | ~v3_ordinal1('#skF_4') | ~r1_tarski(B_143, '#skF_3') | ~r2_hidden(A_142, B_143))), inference(resolution, [status(thm)], [c_441, c_30])).
% 3.38/1.58  tff(c_450, plain, (![A_142, B_143]: (v3_ordinal1('#skF_2'(A_142, B_143)) | ~r1_tarski(B_143, '#skF_3') | ~r2_hidden(A_142, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_446])).
% 3.38/1.58  tff(c_143, plain, (![A_28, B_29, B_69]: (r2_hidden('#skF_2'(A_28, B_29), B_69) | ~r1_tarski(B_29, B_69) | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_28, c_134])).
% 3.38/1.58  tff(c_44, plain, (![C_43]: (v3_ordinal1('#skF_5'(C_43)) | ~r2_hidden(C_43, '#skF_3') | ~v3_ordinal1(C_43))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.38/1.58  tff(c_42, plain, (![C_43]: (r2_hidden('#skF_5'(C_43), '#skF_3') | ~r2_hidden(C_43, '#skF_3') | ~v3_ordinal1(C_43))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.38/1.58  tff(c_32, plain, (![B_39, A_37]: (r2_hidden(B_39, A_37) | r1_ordinal1(A_37, B_39) | ~v3_ordinal1(B_39) | ~v3_ordinal1(A_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.38/1.58  tff(c_243, plain, (![D_86, A_87, B_88]: (~r2_hidden(D_86, '#skF_2'(A_87, B_88)) | ~r2_hidden(D_86, B_88) | ~r2_hidden(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.58  tff(c_618, plain, (![B_171, B_172, A_173]: (~r2_hidden(B_171, B_172) | ~r2_hidden(A_173, B_172) | r1_ordinal1('#skF_2'(A_173, B_172), B_171) | ~v3_ordinal1(B_171) | ~v3_ordinal1('#skF_2'(A_173, B_172)))), inference(resolution, [status(thm)], [c_32, c_243])).
% 3.38/1.58  tff(c_40, plain, (![C_43]: (~r1_ordinal1(C_43, '#skF_5'(C_43)) | ~r2_hidden(C_43, '#skF_3') | ~v3_ordinal1(C_43))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.38/1.58  tff(c_635, plain, (![A_184, B_185]: (~r2_hidden('#skF_2'(A_184, B_185), '#skF_3') | ~r2_hidden('#skF_5'('#skF_2'(A_184, B_185)), B_185) | ~r2_hidden(A_184, B_185) | ~v3_ordinal1('#skF_5'('#skF_2'(A_184, B_185))) | ~v3_ordinal1('#skF_2'(A_184, B_185)))), inference(resolution, [status(thm)], [c_618, c_40])).
% 3.38/1.58  tff(c_802, plain, (![A_214]: (~r2_hidden(A_214, '#skF_3') | ~v3_ordinal1('#skF_5'('#skF_2'(A_214, '#skF_3'))) | ~r2_hidden('#skF_2'(A_214, '#skF_3'), '#skF_3') | ~v3_ordinal1('#skF_2'(A_214, '#skF_3')))), inference(resolution, [status(thm)], [c_42, c_635])).
% 3.38/1.58  tff(c_807, plain, (![A_215]: (~r2_hidden(A_215, '#skF_3') | ~r2_hidden('#skF_2'(A_215, '#skF_3'), '#skF_3') | ~v3_ordinal1('#skF_2'(A_215, '#skF_3')))), inference(resolution, [status(thm)], [c_44, c_802])).
% 3.38/1.58  tff(c_815, plain, (![A_28]: (~v3_ordinal1('#skF_2'(A_28, '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~r2_hidden(A_28, '#skF_3'))), inference(resolution, [status(thm)], [c_143, c_807])).
% 3.38/1.58  tff(c_831, plain, (![A_216]: (~v3_ordinal1('#skF_2'(A_216, '#skF_3')) | ~r2_hidden(A_216, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_815])).
% 3.38/1.58  tff(c_835, plain, (![A_142]: (~r1_tarski('#skF_3', '#skF_3') | ~r2_hidden(A_142, '#skF_3'))), inference(resolution, [status(thm)], [c_450, c_831])).
% 3.38/1.58  tff(c_849, plain, (![A_217]: (~r2_hidden(A_217, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_835])).
% 3.38/1.58  tff(c_887, plain, (![B_218]: (r1_tarski('#skF_3', B_218))), inference(resolution, [status(thm)], [c_6, c_849])).
% 3.38/1.58  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.38/1.58  tff(c_949, plain, (![B_219]: (k2_xboole_0('#skF_3', B_219)=B_219)), inference(resolution, [status(thm)], [c_887, c_8])).
% 3.38/1.58  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.58  tff(c_160, plain, (![A_78, B_79]: (k5_xboole_0(k5_xboole_0(A_78, B_79), k2_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.38/1.58  tff(c_181, plain, (![A_9]: (k5_xboole_0(A_9, k2_xboole_0(A_9, k1_xboole_0))=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_160])).
% 3.38/1.58  tff(c_184, plain, (![A_9]: (k5_xboole_0(A_9, k2_xboole_0(A_9, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_181])).
% 3.38/1.58  tff(c_967, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_949, c_184])).
% 3.38/1.58  tff(c_986, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_967])).
% 3.38/1.58  tff(c_988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_986])).
% 3.38/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.58  
% 3.38/1.58  Inference rules
% 3.38/1.58  ----------------------
% 3.38/1.58  #Ref     : 0
% 3.38/1.58  #Sup     : 207
% 3.38/1.58  #Fact    : 0
% 3.38/1.58  #Define  : 0
% 3.38/1.58  #Split   : 1
% 3.38/1.58  #Chain   : 0
% 3.38/1.58  #Close   : 0
% 3.38/1.58  
% 3.38/1.58  Ordering : KBO
% 3.38/1.58  
% 3.38/1.58  Simplification rules
% 3.38/1.58  ----------------------
% 3.38/1.58  #Subsume      : 47
% 3.38/1.58  #Demod        : 74
% 3.38/1.58  #Tautology    : 59
% 3.38/1.58  #SimpNegUnit  : 2
% 3.38/1.58  #BackRed      : 0
% 3.38/1.58  
% 3.38/1.58  #Partial instantiations: 0
% 3.38/1.58  #Strategies tried      : 1
% 3.38/1.58  
% 3.38/1.58  Timing (in seconds)
% 3.38/1.58  ----------------------
% 3.38/1.58  Preprocessing        : 0.33
% 3.38/1.58  Parsing              : 0.18
% 3.38/1.58  CNF conversion       : 0.02
% 3.38/1.58  Main loop            : 0.44
% 3.38/1.58  Inferencing          : 0.17
% 3.38/1.58  Reduction            : 0.12
% 3.38/1.58  Demodulation         : 0.08
% 3.38/1.58  BG Simplification    : 0.02
% 3.38/1.58  Subsumption          : 0.10
% 3.38/1.58  Abstraction          : 0.02
% 3.38/1.58  MUC search           : 0.00
% 3.38/1.58  Cooper               : 0.00
% 3.38/1.58  Total                : 0.80
% 3.38/1.58  Index Insertion      : 0.00
% 3.38/1.58  Index Deletion       : 0.00
% 3.38/1.58  Index Matching       : 0.00
% 3.38/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
