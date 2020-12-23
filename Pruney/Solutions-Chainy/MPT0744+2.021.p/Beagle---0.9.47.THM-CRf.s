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
% DateTime   : Thu Dec  3 10:06:17 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 130 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 273 expanded)
%              Number of equality atoms :    9 (  26 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_84,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,axiom,(
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

tff(c_44,plain,(
    ! [B_19] : r2_hidden(B_19,k1_ordinal1(B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_96,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ r1_ordinal1(A_16,B_17)
      | ~ v3_ordinal1(B_17)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1090,plain,(
    ! [B_143,A_144] :
      ( r2_hidden(B_143,A_144)
      | B_143 = A_144
      | r2_hidden(A_144,B_143)
      | ~ v3_ordinal1(B_143)
      | ~ v3_ordinal1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden(A_18,B_19)
      | r2_hidden(A_18,k1_ordinal1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_58])).

tff(c_128,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_124])).

tff(c_1214,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1090,c_128])).

tff(c_1411,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_1214])).

tff(c_1461,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1411])).

tff(c_52,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1468,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1461,c_52])).

tff(c_1471,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1468])).

tff(c_1475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_96,c_1471])).

tff(c_1476,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1411])).

tff(c_1481,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1476,c_124])).

tff(c_1486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1481])).

tff(c_1488,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1843,plain,(
    ! [B_192,A_193] :
      ( r2_hidden(B_192,A_193)
      | r1_ordinal1(A_193,B_192)
      | ~ v3_ordinal1(B_192)
      | ~ v3_ordinal1(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1487,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1803,plain,(
    ! [B_187,A_188] :
      ( B_187 = A_188
      | r2_hidden(A_188,B_187)
      | ~ r2_hidden(A_188,k1_ordinal1(B_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1814,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1487,c_1803])).

tff(c_1835,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1814])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1841,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1835,c_2])).

tff(c_1846,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1843,c_1841])).

tff(c_1915,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1846])).

tff(c_1917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1488,c_1915])).

tff(c_1918,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1814])).

tff(c_1923,plain,(
    ~ r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_1488])).

tff(c_1932,plain,(
    ! [B_194,A_195] :
      ( r2_hidden(B_194,A_195)
      | r1_ordinal1(A_195,B_194)
      | ~ v3_ordinal1(B_194)
      | ~ v3_ordinal1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1919,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1814])).

tff(c_1931,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_1919])).

tff(c_1935,plain,
    ( r1_ordinal1('#skF_4','#skF_4')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1932,c_1931])).

tff(c_2001,plain,(
    r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1935])).

tff(c_2003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1923,c_2001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.85  
% 3.59/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.86  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.59/1.86  
% 3.59/1.86  %Foreground sorts:
% 3.59/1.86  
% 3.59/1.86  
% 3.59/1.86  %Background operators:
% 3.59/1.86  
% 3.59/1.86  
% 3.59/1.86  %Foreground operators:
% 3.59/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.59/1.86  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.59/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.59/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.86  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.59/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/1.86  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.59/1.86  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.59/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.86  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.59/1.86  
% 3.69/1.87  tff(f_69, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.69/1.87  tff(f_108, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.69/1.87  tff(f_63, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.69/1.87  tff(f_84, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.69/1.87  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.69/1.87  tff(f_93, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.69/1.87  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.69/1.87  tff(c_44, plain, (![B_19]: (r2_hidden(B_19, k1_ordinal1(B_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.69/1.87  tff(c_56, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.69/1.87  tff(c_54, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.69/1.87  tff(c_64, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.69/1.87  tff(c_96, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 3.69/1.87  tff(c_40, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~r1_ordinal1(A_16, B_17) | ~v3_ordinal1(B_17) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.87  tff(c_1090, plain, (![B_143, A_144]: (r2_hidden(B_143, A_144) | B_143=A_144 | r2_hidden(A_144, B_143) | ~v3_ordinal1(B_143) | ~v3_ordinal1(A_144))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.69/1.87  tff(c_46, plain, (![A_18, B_19]: (~r2_hidden(A_18, B_19) | r2_hidden(A_18, k1_ordinal1(B_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.69/1.87  tff(c_58, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.69/1.87  tff(c_124, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_58])).
% 3.69/1.87  tff(c_128, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_124])).
% 3.69/1.87  tff(c_1214, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1090, c_128])).
% 3.69/1.87  tff(c_1411, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_1214])).
% 3.69/1.87  tff(c_1461, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1411])).
% 3.69/1.87  tff(c_52, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.69/1.87  tff(c_1468, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1461, c_52])).
% 3.69/1.87  tff(c_1471, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1468])).
% 3.69/1.87  tff(c_1475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_96, c_1471])).
% 3.69/1.87  tff(c_1476, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1411])).
% 3.69/1.87  tff(c_1481, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1476, c_124])).
% 3.69/1.87  tff(c_1486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1481])).
% 3.69/1.87  tff(c_1488, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 3.69/1.87  tff(c_1843, plain, (![B_192, A_193]: (r2_hidden(B_192, A_193) | r1_ordinal1(A_193, B_192) | ~v3_ordinal1(B_192) | ~v3_ordinal1(A_193))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.69/1.87  tff(c_1487, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_64])).
% 3.69/1.87  tff(c_1803, plain, (![B_187, A_188]: (B_187=A_188 | r2_hidden(A_188, B_187) | ~r2_hidden(A_188, k1_ordinal1(B_187)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.69/1.87  tff(c_1814, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1487, c_1803])).
% 3.69/1.87  tff(c_1835, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1814])).
% 3.69/1.87  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.69/1.87  tff(c_1841, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1835, c_2])).
% 3.69/1.87  tff(c_1846, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_1843, c_1841])).
% 3.69/1.87  tff(c_1915, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1846])).
% 3.69/1.87  tff(c_1917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1488, c_1915])).
% 3.69/1.87  tff(c_1918, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1814])).
% 3.69/1.87  tff(c_1923, plain, (~r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_1488])).
% 3.69/1.87  tff(c_1932, plain, (![B_194, A_195]: (r2_hidden(B_194, A_195) | r1_ordinal1(A_195, B_194) | ~v3_ordinal1(B_194) | ~v3_ordinal1(A_195))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.69/1.87  tff(c_1919, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1814])).
% 3.69/1.87  tff(c_1931, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_1919])).
% 3.69/1.87  tff(c_1935, plain, (r1_ordinal1('#skF_4', '#skF_4') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1932, c_1931])).
% 3.69/1.87  tff(c_2001, plain, (r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1935])).
% 3.69/1.87  tff(c_2003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1923, c_2001])).
% 3.69/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.87  
% 3.69/1.87  Inference rules
% 3.69/1.87  ----------------------
% 3.69/1.87  #Ref     : 0
% 3.69/1.87  #Sup     : 399
% 3.69/1.87  #Fact    : 2
% 3.69/1.87  #Define  : 0
% 3.69/1.87  #Split   : 5
% 3.69/1.87  #Chain   : 0
% 3.69/1.87  #Close   : 0
% 3.69/1.87  
% 3.69/1.87  Ordering : KBO
% 3.69/1.87  
% 3.69/1.87  Simplification rules
% 3.69/1.87  ----------------------
% 3.69/1.87  #Subsume      : 43
% 3.69/1.87  #Demod        : 43
% 3.69/1.87  #Tautology    : 37
% 3.69/1.87  #SimpNegUnit  : 2
% 3.69/1.87  #BackRed      : 10
% 3.69/1.87  
% 3.69/1.87  #Partial instantiations: 0
% 3.69/1.87  #Strategies tried      : 1
% 3.69/1.87  
% 3.69/1.87  Timing (in seconds)
% 3.69/1.87  ----------------------
% 3.69/1.87  Preprocessing        : 0.48
% 3.69/1.87  Parsing              : 0.24
% 3.69/1.87  CNF conversion       : 0.04
% 3.69/1.87  Main loop            : 0.52
% 3.69/1.87  Inferencing          : 0.18
% 3.69/1.87  Reduction            : 0.15
% 3.69/1.87  Demodulation         : 0.11
% 3.69/1.87  BG Simplification    : 0.03
% 3.69/1.87  Subsumption          : 0.12
% 3.69/1.87  Abstraction          : 0.03
% 3.69/1.87  MUC search           : 0.00
% 3.69/1.87  Cooper               : 0.00
% 3.69/1.87  Total                : 1.04
% 3.69/1.87  Index Insertion      : 0.00
% 3.69/1.87  Index Deletion       : 0.00
% 3.69/1.87  Index Matching       : 0.00
% 3.69/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
