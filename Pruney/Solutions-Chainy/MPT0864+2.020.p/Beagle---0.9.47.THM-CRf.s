%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:11 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 115 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 178 expanded)
%              Number of equality atoms :   51 (  94 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    ! [A_19] : v1_xboole_0('#skF_6'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_606,plain,(
    ! [A_118] :
      ( r2_hidden('#skF_7'(A_118),A_118)
      | k1_xboole_0 = A_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_630,plain,(
    ! [A_120] :
      ( ~ v1_xboole_0(A_120)
      | k1_xboole_0 = A_120 ) ),
    inference(resolution,[status(thm)],[c_606,c_2])).

tff(c_634,plain,(
    ! [A_19] : '#skF_6'(A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_630])).

tff(c_42,plain,(
    ! [A_19] : m1_subset_1('#skF_6'(A_19),k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_635,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_42])).

tff(c_680,plain,(
    ! [A_130,B_131] :
      ( r1_tarski(A_130,B_131)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(B_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_684,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_635,c_680])).

tff(c_170,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_7'(A_58),A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_180,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(A_60)
      | k1_xboole_0 = A_60 ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_184,plain,(
    ! [A_19] : '#skF_6'(A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_180])).

tff(c_185,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_42])).

tff(c_235,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_239,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_185,c_235])).

tff(c_60,plain,
    ( k2_mcart_1('#skF_8') = '#skF_8'
    | k1_mcart_1('#skF_8') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_87,plain,(
    k1_mcart_1('#skF_8') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_62,plain,(
    k4_tarski('#skF_9','#skF_10') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_127,plain,(
    ! [A_54,B_55] : k1_mcart_1(k4_tarski(A_54,B_55)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,(
    k1_mcart_1('#skF_8') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_127])).

tff(c_139,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_136])).

tff(c_140,plain,(
    k4_tarski('#skF_8','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_62])).

tff(c_54,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_7'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_200,plain,(
    ! [C_63,A_64] :
      ( C_63 = A_64
      | ~ r2_hidden(C_63,k1_tarski(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_208,plain,(
    ! [A_64] :
      ( '#skF_7'(k1_tarski(A_64)) = A_64
      | k1_tarski(A_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_200])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_346,plain,(
    ! [C_87,A_88,D_89] :
      ( ~ r2_hidden(C_87,A_88)
      | k4_tarski(C_87,D_89) != '#skF_7'(A_88)
      | k1_xboole_0 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_374,plain,(
    ! [C_96,D_97] :
      ( k4_tarski(C_96,D_97) != '#skF_7'(k1_tarski(C_96))
      | k1_tarski(C_96) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_346])).

tff(c_479,plain,(
    ! [A_108,D_109] :
      ( k4_tarski(A_108,D_109) != A_108
      | k1_tarski(A_108) = k1_xboole_0
      | k1_tarski(A_108) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_374])).

tff(c_483,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_479])).

tff(c_157,plain,(
    ! [B_56,A_57] :
      ( ~ r1_tarski(B_56,A_57)
      | ~ r2_hidden(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_169,plain,(
    ! [C_9] : ~ r1_tarski(k1_tarski(C_9),C_9) ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_502,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_169])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_502])).

tff(c_516,plain,(
    k2_mcart_1('#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_558,plain,(
    ! [A_113,B_114] : k2_mcart_1(k4_tarski(A_113,B_114)) = B_114 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_567,plain,(
    k2_mcart_1('#skF_8') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_558])).

tff(c_570,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_567])).

tff(c_571,plain,(
    k4_tarski('#skF_9','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_62])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_614,plain,(
    ! [A_5] :
      ( '#skF_7'(k1_tarski(A_5)) = A_5
      | k1_tarski(A_5) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_606,c_6])).

tff(c_761,plain,(
    ! [D_143,A_144,C_145] :
      ( ~ r2_hidden(D_143,A_144)
      | k4_tarski(C_145,D_143) != '#skF_7'(A_144)
      | k1_xboole_0 = A_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_801,plain,(
    ! [C_153,C_154] :
      ( k4_tarski(C_153,C_154) != '#skF_7'(k1_tarski(C_154))
      | k1_tarski(C_154) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_761])).

tff(c_905,plain,(
    ! [C_165,A_166] :
      ( k4_tarski(C_165,A_166) != A_166
      | k1_tarski(A_166) = k1_xboole_0
      | k1_tarski(A_166) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_801])).

tff(c_909,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_905])).

tff(c_644,plain,(
    ! [B_122,A_123] :
      ( ~ r1_tarski(B_122,A_123)
      | ~ r2_hidden(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_664,plain,(
    ! [C_9] : ~ r1_tarski(k1_tarski(C_9),C_9) ),
    inference(resolution,[status(thm)],[c_8,c_644])).

tff(c_922,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_664])).

tff(c_941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.50  
% 2.97/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_6
% 2.97/1.50  
% 2.97/1.50  %Foreground sorts:
% 2.97/1.50  
% 2.97/1.50  
% 2.97/1.50  %Background operators:
% 2.97/1.50  
% 2.97/1.50  
% 2.97/1.50  %Foreground operators:
% 2.97/1.50  tff('#skF_7', type, '#skF_7': $i > $i).
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.97/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.97/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.97/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.50  tff('#skF_10', type, '#skF_10': $i).
% 2.97/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.97/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.50  tff('#skF_9', type, '#skF_9': $i).
% 2.97/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.50  tff('#skF_8', type, '#skF_8': $i).
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.50  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.50  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.97/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.50  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.97/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.50  
% 2.97/1.52  tff(f_56, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.97/1.52  tff(f_85, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.97/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.97/1.52  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.97/1.52  tff(f_95, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.97/1.52  tff(f_69, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.97/1.52  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.97/1.52  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.97/1.52  tff(c_40, plain, (![A_19]: (v1_xboole_0('#skF_6'(A_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.97/1.52  tff(c_606, plain, (![A_118]: (r2_hidden('#skF_7'(A_118), A_118) | k1_xboole_0=A_118)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.97/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.52  tff(c_630, plain, (![A_120]: (~v1_xboole_0(A_120) | k1_xboole_0=A_120)), inference(resolution, [status(thm)], [c_606, c_2])).
% 2.97/1.52  tff(c_634, plain, (![A_19]: ('#skF_6'(A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_630])).
% 2.97/1.52  tff(c_42, plain, (![A_19]: (m1_subset_1('#skF_6'(A_19), k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.97/1.52  tff(c_635, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_634, c_42])).
% 2.97/1.52  tff(c_680, plain, (![A_130, B_131]: (r1_tarski(A_130, B_131) | ~m1_subset_1(A_130, k1_zfmisc_1(B_131)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.97/1.52  tff(c_684, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_635, c_680])).
% 2.97/1.52  tff(c_170, plain, (![A_58]: (r2_hidden('#skF_7'(A_58), A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.97/1.52  tff(c_180, plain, (![A_60]: (~v1_xboole_0(A_60) | k1_xboole_0=A_60)), inference(resolution, [status(thm)], [c_170, c_2])).
% 2.97/1.52  tff(c_184, plain, (![A_19]: ('#skF_6'(A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_180])).
% 2.97/1.52  tff(c_185, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_42])).
% 2.97/1.52  tff(c_235, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.97/1.52  tff(c_239, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_185, c_235])).
% 2.97/1.52  tff(c_60, plain, (k2_mcart_1('#skF_8')='#skF_8' | k1_mcart_1('#skF_8')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.97/1.52  tff(c_87, plain, (k1_mcart_1('#skF_8')='#skF_8'), inference(splitLeft, [status(thm)], [c_60])).
% 2.97/1.52  tff(c_62, plain, (k4_tarski('#skF_9', '#skF_10')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.97/1.52  tff(c_127, plain, (![A_54, B_55]: (k1_mcart_1(k4_tarski(A_54, B_55))=A_54)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.97/1.52  tff(c_136, plain, (k1_mcart_1('#skF_8')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_62, c_127])).
% 2.97/1.52  tff(c_139, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_136])).
% 2.97/1.52  tff(c_140, plain, (k4_tarski('#skF_8', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_62])).
% 2.97/1.52  tff(c_54, plain, (![A_27]: (r2_hidden('#skF_7'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.97/1.52  tff(c_200, plain, (![C_63, A_64]: (C_63=A_64 | ~r2_hidden(C_63, k1_tarski(A_64)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.52  tff(c_208, plain, (![A_64]: ('#skF_7'(k1_tarski(A_64))=A_64 | k1_tarski(A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_200])).
% 2.97/1.52  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.52  tff(c_346, plain, (![C_87, A_88, D_89]: (~r2_hidden(C_87, A_88) | k4_tarski(C_87, D_89)!='#skF_7'(A_88) | k1_xboole_0=A_88)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.97/1.52  tff(c_374, plain, (![C_96, D_97]: (k4_tarski(C_96, D_97)!='#skF_7'(k1_tarski(C_96)) | k1_tarski(C_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_346])).
% 2.97/1.52  tff(c_479, plain, (![A_108, D_109]: (k4_tarski(A_108, D_109)!=A_108 | k1_tarski(A_108)=k1_xboole_0 | k1_tarski(A_108)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_374])).
% 2.97/1.52  tff(c_483, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_140, c_479])).
% 2.97/1.52  tff(c_157, plain, (![B_56, A_57]: (~r1_tarski(B_56, A_57) | ~r2_hidden(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.97/1.52  tff(c_169, plain, (![C_9]: (~r1_tarski(k1_tarski(C_9), C_9))), inference(resolution, [status(thm)], [c_8, c_157])).
% 2.97/1.52  tff(c_502, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_483, c_169])).
% 2.97/1.52  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_502])).
% 2.97/1.52  tff(c_516, plain, (k2_mcart_1('#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 2.97/1.52  tff(c_558, plain, (![A_113, B_114]: (k2_mcart_1(k4_tarski(A_113, B_114))=B_114)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.97/1.52  tff(c_567, plain, (k2_mcart_1('#skF_8')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_62, c_558])).
% 2.97/1.52  tff(c_570, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_516, c_567])).
% 2.97/1.52  tff(c_571, plain, (k4_tarski('#skF_9', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_570, c_62])).
% 2.97/1.52  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.52  tff(c_614, plain, (![A_5]: ('#skF_7'(k1_tarski(A_5))=A_5 | k1_tarski(A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_606, c_6])).
% 2.97/1.52  tff(c_761, plain, (![D_143, A_144, C_145]: (~r2_hidden(D_143, A_144) | k4_tarski(C_145, D_143)!='#skF_7'(A_144) | k1_xboole_0=A_144)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.97/1.52  tff(c_801, plain, (![C_153, C_154]: (k4_tarski(C_153, C_154)!='#skF_7'(k1_tarski(C_154)) | k1_tarski(C_154)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_761])).
% 2.97/1.52  tff(c_905, plain, (![C_165, A_166]: (k4_tarski(C_165, A_166)!=A_166 | k1_tarski(A_166)=k1_xboole_0 | k1_tarski(A_166)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_614, c_801])).
% 2.97/1.52  tff(c_909, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_571, c_905])).
% 2.97/1.52  tff(c_644, plain, (![B_122, A_123]: (~r1_tarski(B_122, A_123) | ~r2_hidden(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.97/1.52  tff(c_664, plain, (![C_9]: (~r1_tarski(k1_tarski(C_9), C_9))), inference(resolution, [status(thm)], [c_8, c_644])).
% 2.97/1.52  tff(c_922, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_909, c_664])).
% 2.97/1.52  tff(c_941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_684, c_922])).
% 2.97/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.52  
% 2.97/1.52  Inference rules
% 2.97/1.52  ----------------------
% 2.97/1.52  #Ref     : 0
% 2.97/1.52  #Sup     : 208
% 2.97/1.52  #Fact    : 4
% 2.97/1.52  #Define  : 0
% 2.97/1.52  #Split   : 2
% 2.97/1.52  #Chain   : 0
% 2.97/1.52  #Close   : 0
% 2.97/1.52  
% 2.97/1.52  Ordering : KBO
% 2.97/1.52  
% 2.97/1.52  Simplification rules
% 2.97/1.52  ----------------------
% 2.97/1.52  #Subsume      : 30
% 2.97/1.52  #Demod        : 55
% 2.97/1.52  #Tautology    : 102
% 2.97/1.52  #SimpNegUnit  : 28
% 2.97/1.52  #BackRed      : 7
% 2.97/1.52  
% 2.97/1.52  #Partial instantiations: 0
% 2.97/1.52  #Strategies tried      : 1
% 2.97/1.52  
% 2.97/1.52  Timing (in seconds)
% 2.97/1.52  ----------------------
% 2.97/1.52  Preprocessing        : 0.34
% 2.97/1.52  Parsing              : 0.17
% 2.97/1.52  CNF conversion       : 0.03
% 2.97/1.52  Main loop            : 0.35
% 2.97/1.52  Inferencing          : 0.13
% 2.97/1.52  Reduction            : 0.10
% 2.97/1.52  Demodulation         : 0.07
% 2.97/1.52  BG Simplification    : 0.02
% 2.97/1.52  Subsumption          : 0.06
% 2.97/1.52  Abstraction          : 0.03
% 2.97/1.52  MUC search           : 0.00
% 2.97/1.52  Cooper               : 0.00
% 2.97/1.52  Total                : 0.72
% 2.97/1.52  Index Insertion      : 0.00
% 2.97/1.52  Index Deletion       : 0.00
% 2.97/1.52  Index Matching       : 0.00
% 2.97/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
