%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:08 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 209 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_90,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_68,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_35] : r1_tarski(A_35,A_35) ),
    inference(resolution,[status(thm)],[c_48,c_4])).

tff(c_22,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [C_39,B_40,A_41] :
      ( r2_hidden(C_39,B_40)
      | ~ r2_hidden(C_39,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_58,B_59,B_60] :
      ( r2_hidden('#skF_1'(A_58,B_59),B_60)
      | ~ r1_tarski(A_58,B_60)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_333,plain,(
    ! [A_110,B_111,B_112,B_113] :
      ( r2_hidden('#skF_1'(A_110,B_111),B_112)
      | ~ r1_tarski(B_113,B_112)
      | ~ r1_tarski(A_110,B_113)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_340,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_1'(A_114,B_115),'#skF_5')
      | ~ r1_tarski(A_114,'#skF_4')
      | r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_20,c_333])).

tff(c_360,plain,(
    ! [A_116] :
      ( ~ r1_tarski(A_116,'#skF_4')
      | r1_tarski(A_116,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_340,c_4])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_132,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_3'(A_55,B_56),B_57)
      | ~ r1_tarski(B_56,B_57)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( v3_ordinal1(A_15)
      | ~ r2_hidden(A_15,B_16)
      | ~ v3_ordinal1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    ! [A_55,B_56,B_57] :
      ( v3_ordinal1('#skF_3'(A_55,B_56))
      | ~ v3_ordinal1(B_57)
      | ~ r1_tarski(B_56,B_57)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_132,c_14])).

tff(c_373,plain,(
    ! [A_55,A_116] :
      ( v3_ordinal1('#skF_3'(A_55,A_116))
      | ~ v3_ordinal1('#skF_5')
      | ~ r2_hidden(A_55,A_116)
      | ~ r1_tarski(A_116,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_360,c_144])).

tff(c_388,plain,(
    ! [A_55,A_116] :
      ( v3_ordinal1('#skF_3'(A_55,A_116))
      | ~ r2_hidden(A_55,A_116)
      | ~ r1_tarski(A_116,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_373])).

tff(c_71,plain,(
    ! [A_8,B_9,B_40] :
      ( r2_hidden('#skF_3'(A_8,B_9),B_40)
      | ~ r1_tarski(B_9,B_40)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_28,plain,(
    ! [C_23] :
      ( v3_ordinal1('#skF_6'(C_23))
      | ~ r2_hidden(C_23,'#skF_4')
      | ~ v3_ordinal1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    ! [C_23] :
      ( r2_hidden('#skF_6'(C_23),'#skF_4')
      | ~ r2_hidden(C_23,'#skF_4')
      | ~ v3_ordinal1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [B_19,A_17] :
      ( r2_hidden(B_19,A_17)
      | r1_ordinal1(A_17,B_19)
      | ~ v3_ordinal1(B_19)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    ! [D_52,A_53,B_54] :
      ( ~ r2_hidden(D_52,'#skF_3'(A_53,B_54))
      | ~ r2_hidden(D_52,B_54)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_510,plain,(
    ! [B_141,B_142,A_143] :
      ( ~ r2_hidden(B_141,B_142)
      | ~ r2_hidden(A_143,B_142)
      | r1_ordinal1('#skF_3'(A_143,B_142),B_141)
      | ~ v3_ordinal1(B_141)
      | ~ v3_ordinal1('#skF_3'(A_143,B_142)) ) ),
    inference(resolution,[status(thm)],[c_16,c_106])).

tff(c_24,plain,(
    ! [C_23] :
      ( ~ r1_ordinal1(C_23,'#skF_6'(C_23))
      | ~ r2_hidden(C_23,'#skF_4')
      | ~ v3_ordinal1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_576,plain,(
    ! [A_152,B_153] :
      ( ~ r2_hidden('#skF_3'(A_152,B_153),'#skF_4')
      | ~ r2_hidden('#skF_6'('#skF_3'(A_152,B_153)),B_153)
      | ~ r2_hidden(A_152,B_153)
      | ~ v3_ordinal1('#skF_6'('#skF_3'(A_152,B_153)))
      | ~ v3_ordinal1('#skF_3'(A_152,B_153)) ) ),
    inference(resolution,[status(thm)],[c_510,c_24])).

tff(c_671,plain,(
    ! [A_182] :
      ( ~ r2_hidden(A_182,'#skF_4')
      | ~ v3_ordinal1('#skF_6'('#skF_3'(A_182,'#skF_4')))
      | ~ r2_hidden('#skF_3'(A_182,'#skF_4'),'#skF_4')
      | ~ v3_ordinal1('#skF_3'(A_182,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_26,c_576])).

tff(c_676,plain,(
    ! [A_183] :
      ( ~ r2_hidden(A_183,'#skF_4')
      | ~ r2_hidden('#skF_3'(A_183,'#skF_4'),'#skF_4')
      | ~ v3_ordinal1('#skF_3'(A_183,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_28,c_671])).

tff(c_684,plain,(
    ! [A_8] :
      ( ~ v3_ordinal1('#skF_3'(A_8,'#skF_4'))
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r2_hidden(A_8,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_71,c_676])).

tff(c_700,plain,(
    ! [A_184] :
      ( ~ v3_ordinal1('#skF_3'(A_184,'#skF_4'))
      | ~ r2_hidden(A_184,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_684])).

tff(c_704,plain,(
    ! [A_55] :
      ( ~ r2_hidden(A_55,'#skF_4')
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_388,c_700])).

tff(c_718,plain,(
    ! [A_185] : ~ r2_hidden(A_185,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_704])).

tff(c_758,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_718])).

tff(c_771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.43  
% 2.82/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.44  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1 > #skF_6
% 2.82/1.44  
% 2.82/1.44  %Foreground sorts:
% 2.82/1.44  
% 2.82/1.44  
% 2.82/1.44  %Background operators:
% 2.82/1.44  
% 2.82/1.44  
% 2.82/1.44  %Foreground operators:
% 2.82/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.44  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.82/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.44  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.44  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.82/1.44  
% 2.82/1.45  tff(f_90, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_ordinal1)).
% 2.82/1.45  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.82/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.82/1.45  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.82/1.45  tff(f_59, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 2.82/1.45  tff(f_68, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.82/1.45  tff(c_18, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.45  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.82/1.45  tff(c_48, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), A_35) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.45  tff(c_56, plain, (![A_35]: (r1_tarski(A_35, A_35))), inference(resolution, [status(thm)], [c_48, c_4])).
% 2.82/1.45  tff(c_22, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.45  tff(c_20, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.45  tff(c_60, plain, (![C_39, B_40, A_41]: (r2_hidden(C_39, B_40) | ~r2_hidden(C_39, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.45  tff(c_145, plain, (![A_58, B_59, B_60]: (r2_hidden('#skF_1'(A_58, B_59), B_60) | ~r1_tarski(A_58, B_60) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_6, c_60])).
% 2.82/1.45  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.45  tff(c_333, plain, (![A_110, B_111, B_112, B_113]: (r2_hidden('#skF_1'(A_110, B_111), B_112) | ~r1_tarski(B_113, B_112) | ~r1_tarski(A_110, B_113) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_145, c_2])).
% 2.82/1.45  tff(c_340, plain, (![A_114, B_115]: (r2_hidden('#skF_1'(A_114, B_115), '#skF_5') | ~r1_tarski(A_114, '#skF_4') | r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_20, c_333])).
% 2.82/1.45  tff(c_360, plain, (![A_116]: (~r1_tarski(A_116, '#skF_4') | r1_tarski(A_116, '#skF_5'))), inference(resolution, [status(thm)], [c_340, c_4])).
% 2.82/1.45  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_3'(A_8, B_9), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.82/1.45  tff(c_132, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_3'(A_55, B_56), B_57) | ~r1_tarski(B_56, B_57) | ~r2_hidden(A_55, B_56))), inference(resolution, [status(thm)], [c_12, c_60])).
% 2.82/1.45  tff(c_14, plain, (![A_15, B_16]: (v3_ordinal1(A_15) | ~r2_hidden(A_15, B_16) | ~v3_ordinal1(B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.45  tff(c_144, plain, (![A_55, B_56, B_57]: (v3_ordinal1('#skF_3'(A_55, B_56)) | ~v3_ordinal1(B_57) | ~r1_tarski(B_56, B_57) | ~r2_hidden(A_55, B_56))), inference(resolution, [status(thm)], [c_132, c_14])).
% 2.82/1.45  tff(c_373, plain, (![A_55, A_116]: (v3_ordinal1('#skF_3'(A_55, A_116)) | ~v3_ordinal1('#skF_5') | ~r2_hidden(A_55, A_116) | ~r1_tarski(A_116, '#skF_4'))), inference(resolution, [status(thm)], [c_360, c_144])).
% 2.82/1.45  tff(c_388, plain, (![A_55, A_116]: (v3_ordinal1('#skF_3'(A_55, A_116)) | ~r2_hidden(A_55, A_116) | ~r1_tarski(A_116, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_373])).
% 2.82/1.45  tff(c_71, plain, (![A_8, B_9, B_40]: (r2_hidden('#skF_3'(A_8, B_9), B_40) | ~r1_tarski(B_9, B_40) | ~r2_hidden(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_60])).
% 2.82/1.45  tff(c_28, plain, (![C_23]: (v3_ordinal1('#skF_6'(C_23)) | ~r2_hidden(C_23, '#skF_4') | ~v3_ordinal1(C_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.45  tff(c_26, plain, (![C_23]: (r2_hidden('#skF_6'(C_23), '#skF_4') | ~r2_hidden(C_23, '#skF_4') | ~v3_ordinal1(C_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.45  tff(c_16, plain, (![B_19, A_17]: (r2_hidden(B_19, A_17) | r1_ordinal1(A_17, B_19) | ~v3_ordinal1(B_19) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.45  tff(c_106, plain, (![D_52, A_53, B_54]: (~r2_hidden(D_52, '#skF_3'(A_53, B_54)) | ~r2_hidden(D_52, B_54) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.82/1.45  tff(c_510, plain, (![B_141, B_142, A_143]: (~r2_hidden(B_141, B_142) | ~r2_hidden(A_143, B_142) | r1_ordinal1('#skF_3'(A_143, B_142), B_141) | ~v3_ordinal1(B_141) | ~v3_ordinal1('#skF_3'(A_143, B_142)))), inference(resolution, [status(thm)], [c_16, c_106])).
% 2.82/1.45  tff(c_24, plain, (![C_23]: (~r1_ordinal1(C_23, '#skF_6'(C_23)) | ~r2_hidden(C_23, '#skF_4') | ~v3_ordinal1(C_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.45  tff(c_576, plain, (![A_152, B_153]: (~r2_hidden('#skF_3'(A_152, B_153), '#skF_4') | ~r2_hidden('#skF_6'('#skF_3'(A_152, B_153)), B_153) | ~r2_hidden(A_152, B_153) | ~v3_ordinal1('#skF_6'('#skF_3'(A_152, B_153))) | ~v3_ordinal1('#skF_3'(A_152, B_153)))), inference(resolution, [status(thm)], [c_510, c_24])).
% 2.82/1.45  tff(c_671, plain, (![A_182]: (~r2_hidden(A_182, '#skF_4') | ~v3_ordinal1('#skF_6'('#skF_3'(A_182, '#skF_4'))) | ~r2_hidden('#skF_3'(A_182, '#skF_4'), '#skF_4') | ~v3_ordinal1('#skF_3'(A_182, '#skF_4')))), inference(resolution, [status(thm)], [c_26, c_576])).
% 2.82/1.45  tff(c_676, plain, (![A_183]: (~r2_hidden(A_183, '#skF_4') | ~r2_hidden('#skF_3'(A_183, '#skF_4'), '#skF_4') | ~v3_ordinal1('#skF_3'(A_183, '#skF_4')))), inference(resolution, [status(thm)], [c_28, c_671])).
% 2.82/1.45  tff(c_684, plain, (![A_8]: (~v3_ordinal1('#skF_3'(A_8, '#skF_4')) | ~r1_tarski('#skF_4', '#skF_4') | ~r2_hidden(A_8, '#skF_4'))), inference(resolution, [status(thm)], [c_71, c_676])).
% 2.82/1.45  tff(c_700, plain, (![A_184]: (~v3_ordinal1('#skF_3'(A_184, '#skF_4')) | ~r2_hidden(A_184, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_684])).
% 2.82/1.45  tff(c_704, plain, (![A_55]: (~r2_hidden(A_55, '#skF_4') | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_388, c_700])).
% 2.82/1.45  tff(c_718, plain, (![A_185]: (~r2_hidden(A_185, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_704])).
% 2.82/1.45  tff(c_758, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_718])).
% 2.82/1.45  tff(c_771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_758])).
% 2.82/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.45  
% 2.82/1.45  Inference rules
% 2.82/1.45  ----------------------
% 2.82/1.45  #Ref     : 0
% 2.82/1.45  #Sup     : 158
% 2.82/1.45  #Fact    : 0
% 2.82/1.45  #Define  : 0
% 2.82/1.45  #Split   : 2
% 2.82/1.45  #Chain   : 0
% 2.82/1.45  #Close   : 0
% 2.82/1.45  
% 2.82/1.45  Ordering : KBO
% 2.82/1.45  
% 2.82/1.45  Simplification rules
% 2.82/1.45  ----------------------
% 3.12/1.45  #Subsume      : 67
% 3.12/1.45  #Demod        : 14
% 3.12/1.45  #Tautology    : 2
% 3.12/1.45  #SimpNegUnit  : 4
% 3.12/1.45  #BackRed      : 0
% 3.12/1.45  
% 3.12/1.45  #Partial instantiations: 0
% 3.12/1.45  #Strategies tried      : 1
% 3.12/1.45  
% 3.12/1.45  Timing (in seconds)
% 3.12/1.45  ----------------------
% 3.12/1.45  Preprocessing        : 0.29
% 3.12/1.45  Parsing              : 0.16
% 3.12/1.45  CNF conversion       : 0.02
% 3.12/1.45  Main loop            : 0.39
% 3.12/1.45  Inferencing          : 0.16
% 3.12/1.45  Reduction            : 0.09
% 3.12/1.46  Demodulation         : 0.06
% 3.12/1.46  BG Simplification    : 0.02
% 3.12/1.46  Subsumption          : 0.11
% 3.12/1.46  Abstraction          : 0.01
% 3.12/1.46  MUC search           : 0.00
% 3.12/1.46  Cooper               : 0.00
% 3.12/1.46  Total                : 0.72
% 3.12/1.46  Index Insertion      : 0.00
% 3.12/1.46  Index Deletion       : 0.00
% 3.12/1.46  Index Matching       : 0.00
% 3.12/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
