%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:20 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   64 (  94 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 201 expanded)
%              Number of equality atoms :   41 ( 158 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_72,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_70,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_85,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_54,plain,(
    ! [B_34] : r1_tarski(k1_tarski(B_34),k1_tarski(B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_190,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(A_60,C_61)
      | ~ r1_tarski(k2_xboole_0(A_60,B_62),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_229,plain,(
    ! [C_65] :
      ( r1_tarski('#skF_7',C_65)
      | ~ r1_tarski(k1_tarski('#skF_6'),C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_190])).

tff(c_244,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_229])).

tff(c_513,plain,(
    ! [B_95,A_96] :
      ( k1_tarski(B_95) = A_96
      | k1_xboole_0 = A_96
      | ~ r1_tarski(A_96,k1_tarski(B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_528,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_244,c_513])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_85,c_528])).

tff(c_543,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_544,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_30,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_545,plain,(
    ! [A_17] : r1_tarski('#skF_7',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_30])).

tff(c_615,plain,(
    ! [A_111,B_112] :
      ( k2_xboole_0(A_111,B_112) = B_112
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_635,plain,(
    ! [A_17] : k2_xboole_0('#skF_7',A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_545,c_615])).

tff(c_645,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_76])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_645])).

tff(c_648,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_649,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_683,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_649,c_74])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_650,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_76])).

tff(c_878,plain,(
    ! [D_140,B_141,A_142] :
      ( ~ r2_hidden(D_140,B_141)
      | r2_hidden(D_140,k2_xboole_0(A_142,B_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_902,plain,(
    ! [D_143] :
      ( ~ r2_hidden(D_143,'#skF_8')
      | r2_hidden(D_143,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_878])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1190,plain,(
    ! [A_172] :
      ( r1_tarski(A_172,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_172,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_902,c_4])).

tff(c_1195,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_1190])).

tff(c_1237,plain,(
    ! [B_174,A_175] :
      ( k1_tarski(B_174) = A_175
      | k1_xboole_0 = A_175
      | ~ r1_tarski(A_175,k1_tarski(B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1252,plain,(
    ! [A_175] :
      ( k1_tarski('#skF_6') = A_175
      | k1_xboole_0 = A_175
      | ~ r1_tarski(A_175,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_1237])).

tff(c_1365,plain,(
    ! [A_180] :
      ( A_180 = '#skF_7'
      | k1_xboole_0 = A_180
      | ~ r1_tarski(A_180,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_1252])).

tff(c_1368,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1195,c_1365])).

tff(c_1388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_683,c_1368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.49  
% 3.08/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.49  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.08/1.49  
% 3.08/1.49  %Foreground sorts:
% 3.08/1.49  
% 3.08/1.49  
% 3.08/1.49  %Background operators:
% 3.08/1.49  
% 3.08/1.49  
% 3.08/1.49  %Foreground operators:
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.08/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.08/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.08/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.08/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.08/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.08/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.08/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.08/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.08/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.08/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.08/1.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.08/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.08/1.49  
% 3.14/1.50  tff(f_108, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.14/1.50  tff(f_72, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.14/1.50  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.14/1.50  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.14/1.50  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.14/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.14/1.50  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.14/1.50  tff(c_72, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.14/1.50  tff(c_86, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_72])).
% 3.14/1.50  tff(c_70, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.14/1.50  tff(c_85, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_70])).
% 3.14/1.50  tff(c_54, plain, (![B_34]: (r1_tarski(k1_tarski(B_34), k1_tarski(B_34)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.50  tff(c_76, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.14/1.50  tff(c_190, plain, (![A_60, C_61, B_62]: (r1_tarski(A_60, C_61) | ~r1_tarski(k2_xboole_0(A_60, B_62), C_61))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.50  tff(c_229, plain, (![C_65]: (r1_tarski('#skF_7', C_65) | ~r1_tarski(k1_tarski('#skF_6'), C_65))), inference(superposition, [status(thm), theory('equality')], [c_76, c_190])).
% 3.14/1.50  tff(c_244, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_229])).
% 3.14/1.50  tff(c_513, plain, (![B_95, A_96]: (k1_tarski(B_95)=A_96 | k1_xboole_0=A_96 | ~r1_tarski(A_96, k1_tarski(B_95)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.50  tff(c_528, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_244, c_513])).
% 3.14/1.50  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_85, c_528])).
% 3.14/1.50  tff(c_543, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_72])).
% 3.14/1.50  tff(c_544, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_72])).
% 3.14/1.50  tff(c_30, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.14/1.50  tff(c_545, plain, (![A_17]: (r1_tarski('#skF_7', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_544, c_30])).
% 3.14/1.50  tff(c_615, plain, (![A_111, B_112]: (k2_xboole_0(A_111, B_112)=B_112 | ~r1_tarski(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.14/1.50  tff(c_635, plain, (![A_17]: (k2_xboole_0('#skF_7', A_17)=A_17)), inference(resolution, [status(thm)], [c_545, c_615])).
% 3.14/1.50  tff(c_645, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_635, c_76])).
% 3.14/1.50  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_543, c_645])).
% 3.14/1.50  tff(c_648, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 3.14/1.50  tff(c_649, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_70])).
% 3.14/1.50  tff(c_74, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.14/1.50  tff(c_683, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_649, c_649, c_74])).
% 3.14/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.50  tff(c_650, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_649, c_76])).
% 3.14/1.50  tff(c_878, plain, (![D_140, B_141, A_142]: (~r2_hidden(D_140, B_141) | r2_hidden(D_140, k2_xboole_0(A_142, B_141)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.50  tff(c_902, plain, (![D_143]: (~r2_hidden(D_143, '#skF_8') | r2_hidden(D_143, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_650, c_878])).
% 3.14/1.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.50  tff(c_1190, plain, (![A_172]: (r1_tarski(A_172, '#skF_7') | ~r2_hidden('#skF_1'(A_172, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_902, c_4])).
% 3.14/1.50  tff(c_1195, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_1190])).
% 3.14/1.50  tff(c_1237, plain, (![B_174, A_175]: (k1_tarski(B_174)=A_175 | k1_xboole_0=A_175 | ~r1_tarski(A_175, k1_tarski(B_174)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.50  tff(c_1252, plain, (![A_175]: (k1_tarski('#skF_6')=A_175 | k1_xboole_0=A_175 | ~r1_tarski(A_175, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_649, c_1237])).
% 3.14/1.50  tff(c_1365, plain, (![A_180]: (A_180='#skF_7' | k1_xboole_0=A_180 | ~r1_tarski(A_180, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_649, c_1252])).
% 3.14/1.50  tff(c_1368, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1195, c_1365])).
% 3.14/1.50  tff(c_1388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_648, c_683, c_1368])).
% 3.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  Inference rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Ref     : 0
% 3.14/1.50  #Sup     : 300
% 3.14/1.50  #Fact    : 0
% 3.14/1.50  #Define  : 0
% 3.14/1.50  #Split   : 3
% 3.14/1.50  #Chain   : 0
% 3.14/1.50  #Close   : 0
% 3.14/1.50  
% 3.14/1.50  Ordering : KBO
% 3.14/1.50  
% 3.14/1.50  Simplification rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Subsume      : 5
% 3.14/1.50  #Demod        : 125
% 3.14/1.50  #Tautology    : 190
% 3.14/1.50  #SimpNegUnit  : 7
% 3.14/1.50  #BackRed      : 6
% 3.14/1.50  
% 3.14/1.50  #Partial instantiations: 0
% 3.14/1.50  #Strategies tried      : 1
% 3.14/1.50  
% 3.14/1.50  Timing (in seconds)
% 3.14/1.50  ----------------------
% 3.14/1.51  Preprocessing        : 0.34
% 3.14/1.51  Parsing              : 0.17
% 3.14/1.51  CNF conversion       : 0.03
% 3.14/1.51  Main loop            : 0.40
% 3.14/1.51  Inferencing          : 0.15
% 3.14/1.51  Reduction            : 0.13
% 3.14/1.51  Demodulation         : 0.10
% 3.14/1.51  BG Simplification    : 0.02
% 3.14/1.51  Subsumption          : 0.06
% 3.14/1.51  Abstraction          : 0.02
% 3.14/1.51  MUC search           : 0.00
% 3.14/1.51  Cooper               : 0.00
% 3.14/1.51  Total                : 0.77
% 3.14/1.51  Index Insertion      : 0.00
% 3.14/1.51  Index Deletion       : 0.00
% 3.14/1.51  Index Matching       : 0.00
% 3.14/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
