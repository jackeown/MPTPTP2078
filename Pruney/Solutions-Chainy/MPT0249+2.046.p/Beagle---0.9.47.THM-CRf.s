%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:29 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 224 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  103 ( 411 expanded)
%              Number of equality atoms :   39 ( 248 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_66,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_68,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_85,plain,(
    ! [A_44,B_45] : r1_tarski(A_44,k2_xboole_0(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_85])).

tff(c_291,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_298,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88,c_291])).

tff(c_306,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_298])).

tff(c_311,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_68])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_410,plain,(
    ! [C_79] :
      ( C_79 = '#skF_7'
      | ~ r2_hidden(C_79,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_34])).

tff(c_526,plain,(
    ! [B_91] :
      ( '#skF_1'('#skF_8',B_91) = '#skF_7'
      | r1_tarski('#skF_8',B_91) ) ),
    inference(resolution,[status(thm)],[c_6,c_410])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_692,plain,(
    ! [B_102] :
      ( k2_xboole_0('#skF_8',B_102) = B_102
      | '#skF_1'('#skF_8',B_102) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_526,c_28])).

tff(c_711,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_311])).

tff(c_736,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_711])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_748,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_4])).

tff(c_754,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_32,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_359,plain,(
    ! [C_75,B_76,A_77] :
      ( r2_hidden(C_75,B_76)
      | ~ r2_hidden(C_75,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_471,plain,(
    ! [C_85,B_86] :
      ( r2_hidden(C_85,B_86)
      | ~ r1_tarski(k1_tarski(C_85),B_86) ) ),
    inference(resolution,[status(thm)],[c_36,c_359])).

tff(c_486,plain,(
    ! [C_87,B_88] : r2_hidden(C_87,k2_xboole_0(k1_tarski(C_87),B_88)) ),
    inference(resolution,[status(thm)],[c_32,c_471])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_992,plain,(
    ! [C_125,B_126,B_127] :
      ( r2_hidden(C_125,B_126)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(C_125),B_127),B_126) ) ),
    inference(resolution,[status(thm)],[c_486,c_2])).

tff(c_1014,plain,(
    ! [C_125,B_127,B_20] : r2_hidden(C_125,k2_xboole_0(k2_xboole_0(k1_tarski(C_125),B_127),B_20)) ),
    inference(resolution,[status(thm)],[c_32,c_992])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,k4_xboole_0(A_6,B_7))
      | r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_619,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k4_xboole_0(A_95,B_96),C_97) = k4_xboole_0(A_95,k2_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1230,plain,(
    ! [D_148,C_149,A_150,B_151] :
      ( ~ r2_hidden(D_148,C_149)
      | ~ r2_hidden(D_148,k4_xboole_0(A_150,k2_xboole_0(B_151,C_149))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_10])).

tff(c_1283,plain,(
    ! [D_152,A_153] :
      ( ~ r2_hidden(D_152,'#skF_9')
      | ~ r2_hidden(D_152,k4_xboole_0(A_153,'#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_1230])).

tff(c_1318,plain,(
    ! [D_154,A_155] :
      ( ~ r2_hidden(D_154,'#skF_9')
      | r2_hidden(D_154,'#skF_8')
      | ~ r2_hidden(D_154,A_155) ) ),
    inference(resolution,[status(thm)],[c_8,c_1283])).

tff(c_1333,plain,(
    ! [A_155] :
      ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_4'('#skF_9'),A_155)
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_26,c_1318])).

tff(c_1342,plain,(
    ! [A_155] :
      ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_4'('#skF_9'),A_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1333])).

tff(c_1350,plain,(
    ! [A_158] : ~ r2_hidden('#skF_4'('#skF_9'),A_158) ),
    inference(splitLeft,[status(thm)],[c_1342])).

tff(c_1375,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1014,c_1350])).

tff(c_1376,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1342])).

tff(c_332,plain,(
    ! [C_25] :
      ( C_25 = '#skF_7'
      | ~ r2_hidden(C_25,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_34])).

tff(c_1382,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1376,c_332])).

tff(c_1392,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1382,c_26])).

tff(c_1397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_754,c_1392])).

tff(c_1398,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_1402,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1398,c_28])).

tff(c_1404,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_1402])).

tff(c_1406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.51  
% 2.93/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.52  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 2.93/1.52  
% 2.93/1.52  %Foreground sorts:
% 2.93/1.52  
% 2.93/1.52  
% 2.93/1.52  %Background operators:
% 2.93/1.52  
% 2.93/1.52  
% 2.93/1.52  %Foreground operators:
% 2.93/1.52  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.93/1.52  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.93/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.52  tff('#skF_7', type, '#skF_7': $i).
% 2.93/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.93/1.52  tff('#skF_9', type, '#skF_9': $i).
% 2.93/1.52  tff('#skF_8', type, '#skF_8': $i).
% 2.93/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.93/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.93/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.93/1.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.93/1.52  
% 3.21/1.53  tff(f_94, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.21/1.53  tff(f_58, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.21/1.53  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.21/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.21/1.53  tff(f_65, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.21/1.53  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.21/1.53  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.21/1.53  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.21/1.53  tff(f_56, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.21/1.53  tff(c_66, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.53  tff(c_64, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.53  tff(c_68, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.53  tff(c_85, plain, (![A_44, B_45]: (r1_tarski(A_44, k2_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.53  tff(c_88, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_85])).
% 3.21/1.53  tff(c_291, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.21/1.53  tff(c_298, plain, (k1_tarski('#skF_7')='#skF_8' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_88, c_291])).
% 3.21/1.53  tff(c_306, plain, (k1_tarski('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_64, c_298])).
% 3.21/1.53  tff(c_311, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_306, c_68])).
% 3.21/1.53  tff(c_62, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.53  tff(c_34, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.53  tff(c_410, plain, (![C_79]: (C_79='#skF_7' | ~r2_hidden(C_79, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_34])).
% 3.21/1.53  tff(c_526, plain, (![B_91]: ('#skF_1'('#skF_8', B_91)='#skF_7' | r1_tarski('#skF_8', B_91))), inference(resolution, [status(thm)], [c_6, c_410])).
% 3.21/1.53  tff(c_28, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.21/1.53  tff(c_692, plain, (![B_102]: (k2_xboole_0('#skF_8', B_102)=B_102 | '#skF_1'('#skF_8', B_102)='#skF_7')), inference(resolution, [status(thm)], [c_526, c_28])).
% 3.21/1.53  tff(c_711, plain, ('#skF_9'='#skF_8' | '#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_692, c_311])).
% 3.21/1.53  tff(c_736, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_66, c_711])).
% 3.21/1.53  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.53  tff(c_748, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_736, c_4])).
% 3.21/1.53  tff(c_754, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_748])).
% 3.21/1.53  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.53  tff(c_36, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.53  tff(c_359, plain, (![C_75, B_76, A_77]: (r2_hidden(C_75, B_76) | ~r2_hidden(C_75, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.53  tff(c_471, plain, (![C_85, B_86]: (r2_hidden(C_85, B_86) | ~r1_tarski(k1_tarski(C_85), B_86))), inference(resolution, [status(thm)], [c_36, c_359])).
% 3.21/1.53  tff(c_486, plain, (![C_87, B_88]: (r2_hidden(C_87, k2_xboole_0(k1_tarski(C_87), B_88)))), inference(resolution, [status(thm)], [c_32, c_471])).
% 3.21/1.53  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.53  tff(c_992, plain, (![C_125, B_126, B_127]: (r2_hidden(C_125, B_126) | ~r1_tarski(k2_xboole_0(k1_tarski(C_125), B_127), B_126))), inference(resolution, [status(thm)], [c_486, c_2])).
% 3.21/1.53  tff(c_1014, plain, (![C_125, B_127, B_20]: (r2_hidden(C_125, k2_xboole_0(k2_xboole_0(k1_tarski(C_125), B_127), B_20)))), inference(resolution, [status(thm)], [c_32, c_992])).
% 3.21/1.53  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.53  tff(c_8, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, k4_xboole_0(A_6, B_7)) | r2_hidden(D_11, B_7) | ~r2_hidden(D_11, A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.21/1.53  tff(c_619, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k4_xboole_0(A_95, B_96), C_97)=k4_xboole_0(A_95, k2_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.53  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.21/1.53  tff(c_1230, plain, (![D_148, C_149, A_150, B_151]: (~r2_hidden(D_148, C_149) | ~r2_hidden(D_148, k4_xboole_0(A_150, k2_xboole_0(B_151, C_149))))), inference(superposition, [status(thm), theory('equality')], [c_619, c_10])).
% 3.21/1.53  tff(c_1283, plain, (![D_152, A_153]: (~r2_hidden(D_152, '#skF_9') | ~r2_hidden(D_152, k4_xboole_0(A_153, '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_311, c_1230])).
% 3.21/1.53  tff(c_1318, plain, (![D_154, A_155]: (~r2_hidden(D_154, '#skF_9') | r2_hidden(D_154, '#skF_8') | ~r2_hidden(D_154, A_155))), inference(resolution, [status(thm)], [c_8, c_1283])).
% 3.21/1.53  tff(c_1333, plain, (![A_155]: (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | ~r2_hidden('#skF_4'('#skF_9'), A_155) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_26, c_1318])).
% 3.21/1.53  tff(c_1342, plain, (![A_155]: (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | ~r2_hidden('#skF_4'('#skF_9'), A_155))), inference(negUnitSimplification, [status(thm)], [c_62, c_1333])).
% 3.21/1.53  tff(c_1350, plain, (![A_158]: (~r2_hidden('#skF_4'('#skF_9'), A_158))), inference(splitLeft, [status(thm)], [c_1342])).
% 3.21/1.53  tff(c_1375, plain, $false, inference(resolution, [status(thm)], [c_1014, c_1350])).
% 3.21/1.53  tff(c_1376, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_1342])).
% 3.21/1.53  tff(c_332, plain, (![C_25]: (C_25='#skF_7' | ~r2_hidden(C_25, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_34])).
% 3.21/1.53  tff(c_1382, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_1376, c_332])).
% 3.21/1.53  tff(c_1392, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_1382, c_26])).
% 3.21/1.53  tff(c_1397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_754, c_1392])).
% 3.21/1.53  tff(c_1398, plain, (r1_tarski('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_748])).
% 3.21/1.53  tff(c_1402, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_1398, c_28])).
% 3.21/1.53  tff(c_1404, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_311, c_1402])).
% 3.21/1.53  tff(c_1406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1404])).
% 3.21/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.53  
% 3.21/1.53  Inference rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Ref     : 0
% 3.21/1.53  #Sup     : 307
% 3.21/1.53  #Fact    : 0
% 3.21/1.53  #Define  : 0
% 3.21/1.53  #Split   : 3
% 3.21/1.53  #Chain   : 0
% 3.21/1.53  #Close   : 0
% 3.21/1.53  
% 3.21/1.53  Ordering : KBO
% 3.21/1.53  
% 3.21/1.53  Simplification rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Subsume      : 41
% 3.21/1.53  #Demod        : 113
% 3.21/1.53  #Tautology    : 157
% 3.21/1.53  #SimpNegUnit  : 21
% 3.21/1.53  #BackRed      : 6
% 3.21/1.53  
% 3.21/1.53  #Partial instantiations: 0
% 3.21/1.53  #Strategies tried      : 1
% 3.21/1.53  
% 3.21/1.53  Timing (in seconds)
% 3.21/1.53  ----------------------
% 3.21/1.53  Preprocessing        : 0.31
% 3.21/1.54  Parsing              : 0.16
% 3.21/1.54  CNF conversion       : 0.03
% 3.21/1.54  Main loop            : 0.41
% 3.21/1.54  Inferencing          : 0.14
% 3.21/1.54  Reduction            : 0.14
% 3.21/1.54  Demodulation         : 0.10
% 3.21/1.54  BG Simplification    : 0.02
% 3.21/1.54  Subsumption          : 0.08
% 3.21/1.54  Abstraction          : 0.02
% 3.21/1.54  MUC search           : 0.00
% 3.21/1.54  Cooper               : 0.00
% 3.21/1.54  Total                : 0.76
% 3.21/1.54  Index Insertion      : 0.00
% 3.21/1.54  Index Deletion       : 0.00
% 3.21/1.54  Index Matching       : 0.00
% 3.21/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
