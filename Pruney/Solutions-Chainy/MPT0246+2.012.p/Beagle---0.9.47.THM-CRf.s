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
% DateTime   : Thu Dec  3 09:50:01 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 194 expanded)
%              Number of leaves         :   22 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 370 expanded)
%              Number of equality atoms :   47 ( 158 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_54,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_450,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_1'(A_89,B_90,C_91),A_89)
      | r2_hidden('#skF_2'(A_89,B_90,C_91),C_91)
      | k4_xboole_0(A_89,B_90) = C_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k1_tarski(A_17),B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_46,plain,(
    ! [B_22] : k4_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) != k1_tarski(B_22) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_98,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_46])).

tff(c_44,plain,(
    ! [B_20] : r1_tarski(k1_xboole_0,k1_tarski(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_129,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_135,plain,(
    ! [B_20] :
      ( k1_tarski(B_20) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_20),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_129])).

tff(c_148,plain,(
    ! [B_46] : ~ r1_tarski(k1_tarski(B_46),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_135])).

tff(c_156,plain,(
    ! [A_17] : ~ r2_hidden(A_17,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_148])).

tff(c_521,plain,(
    ! [B_92,C_93] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_92,C_93),C_93)
      | k4_xboole_0(k1_xboole_0,B_92) = C_93 ) ),
    inference(resolution,[status(thm)],[c_450,c_156])).

tff(c_558,plain,(
    ! [B_92] : k4_xboole_0(k1_xboole_0,B_92) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_521,c_156])).

tff(c_513,plain,(
    ! [B_90,C_91] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_90,C_91),C_91)
      | k4_xboole_0(k1_xboole_0,B_90) = C_91 ) ),
    inference(resolution,[status(thm)],[c_450,c_156])).

tff(c_624,plain,(
    ! [B_96,C_97] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_96,C_97),C_97)
      | k1_xboole_0 = C_97 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_513])).

tff(c_50,plain,(
    ! [C_24] :
      ( C_24 = '#skF_4'
      | ~ r2_hidden(C_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_654,plain,(
    ! [B_96] :
      ( '#skF_2'(k1_xboole_0,B_96,'#skF_3') = '#skF_4'
      | k1_xboole_0 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_624,c_50])).

tff(c_674,plain,(
    ! [B_98] : '#skF_2'(k1_xboole_0,B_98,'#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_654])).

tff(c_560,plain,(
    ! [B_90,C_91] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_90,C_91),C_91)
      | k1_xboole_0 = C_91 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_513])).

tff(c_679,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_560])).

tff(c_684,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_679])).

tff(c_114,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | ~ r1_tarski(k1_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,(
    ! [A_41] : r2_hidden(A_41,k1_tarski(A_41)) ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_686,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r2_hidden('#skF_1'(A_99,B_100,C_101),B_100)
      | r2_hidden('#skF_2'(A_99,B_100,C_101),C_101)
      | k4_xboole_0(A_99,B_100) = C_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_689,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_686])).

tff(c_720,plain,(
    ! [A_104,C_105] :
      ( r2_hidden('#skF_2'(A_104,A_104,C_105),C_105)
      | k1_xboole_0 = C_105 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_689])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1765,plain,(
    ! [A_149,A_150,B_151] :
      ( r2_hidden('#skF_2'(A_149,A_149,k4_xboole_0(A_150,B_151)),A_150)
      | k4_xboole_0(A_150,B_151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_720,c_6])).

tff(c_1846,plain,(
    ! [A_152,B_153] :
      ( '#skF_2'(A_152,A_152,k4_xboole_0('#skF_3',B_153)) = '#skF_4'
      | k4_xboole_0('#skF_3',B_153) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1765,c_50])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_772,plain,(
    ! [A_104,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_104,A_104,k4_xboole_0(A_1,B_2)),B_2)
      | k4_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_720,c_4])).

tff(c_1901,plain,(
    ! [B_154] :
      ( ~ r2_hidden('#skF_4',B_154)
      | k4_xboole_0('#skF_3',B_154) = k1_xboole_0
      | k4_xboole_0('#skF_3',B_154) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1846,c_772])).

tff(c_1920,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128,c_1901])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_309,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | k4_xboole_0(A_71,B_70) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_129])).

tff(c_322,plain,(
    ! [A_17,B_18] :
      ( k1_tarski(A_17) = B_18
      | k4_xboole_0(B_18,k1_tarski(A_17)) != k1_xboole_0
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_38,c_309])).

tff(c_1954,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1920,c_322])).

tff(c_1987,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_1954])).

tff(c_1989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.55  
% 3.14/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.55  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.14/1.55  
% 3.14/1.55  %Foreground sorts:
% 3.14/1.55  
% 3.14/1.55  
% 3.14/1.55  %Background operators:
% 3.14/1.55  
% 3.14/1.55  
% 3.14/1.55  %Foreground operators:
% 3.14/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.55  
% 3.57/1.56  tff(f_81, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.57/1.56  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.57/1.56  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.57/1.56  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.57/1.56  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.57/1.56  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.57/1.56  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.57/1.56  tff(c_54, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.57/1.56  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.57/1.56  tff(c_450, plain, (![A_89, B_90, C_91]: (r2_hidden('#skF_1'(A_89, B_90, C_91), A_89) | r2_hidden('#skF_2'(A_89, B_90, C_91), C_91) | k4_xboole_0(A_89, B_90)=C_91)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.56  tff(c_38, plain, (![A_17, B_18]: (r1_tarski(k1_tarski(A_17), B_18) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.57/1.56  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.56  tff(c_81, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.56  tff(c_97, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_81])).
% 3.57/1.56  tff(c_46, plain, (![B_22]: (k4_xboole_0(k1_tarski(B_22), k1_tarski(B_22))!=k1_tarski(B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.57/1.56  tff(c_98, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_46])).
% 3.57/1.56  tff(c_44, plain, (![B_20]: (r1_tarski(k1_xboole_0, k1_tarski(B_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.57/1.56  tff(c_129, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.56  tff(c_135, plain, (![B_20]: (k1_tarski(B_20)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_20), k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_129])).
% 3.57/1.56  tff(c_148, plain, (![B_46]: (~r1_tarski(k1_tarski(B_46), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_98, c_135])).
% 3.57/1.56  tff(c_156, plain, (![A_17]: (~r2_hidden(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_148])).
% 3.57/1.56  tff(c_521, plain, (![B_92, C_93]: (r2_hidden('#skF_2'(k1_xboole_0, B_92, C_93), C_93) | k4_xboole_0(k1_xboole_0, B_92)=C_93)), inference(resolution, [status(thm)], [c_450, c_156])).
% 3.57/1.56  tff(c_558, plain, (![B_92]: (k4_xboole_0(k1_xboole_0, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_521, c_156])).
% 3.57/1.56  tff(c_513, plain, (![B_90, C_91]: (r2_hidden('#skF_2'(k1_xboole_0, B_90, C_91), C_91) | k4_xboole_0(k1_xboole_0, B_90)=C_91)), inference(resolution, [status(thm)], [c_450, c_156])).
% 3.57/1.56  tff(c_624, plain, (![B_96, C_97]: (r2_hidden('#skF_2'(k1_xboole_0, B_96, C_97), C_97) | k1_xboole_0=C_97)), inference(demodulation, [status(thm), theory('equality')], [c_558, c_513])).
% 3.57/1.56  tff(c_50, plain, (![C_24]: (C_24='#skF_4' | ~r2_hidden(C_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.57/1.56  tff(c_654, plain, (![B_96]: ('#skF_2'(k1_xboole_0, B_96, '#skF_3')='#skF_4' | k1_xboole_0='#skF_3')), inference(resolution, [status(thm)], [c_624, c_50])).
% 3.57/1.56  tff(c_674, plain, (![B_98]: ('#skF_2'(k1_xboole_0, B_98, '#skF_3')='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_654])).
% 3.57/1.56  tff(c_560, plain, (![B_90, C_91]: (r2_hidden('#skF_2'(k1_xboole_0, B_90, C_91), C_91) | k1_xboole_0=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_558, c_513])).
% 3.57/1.56  tff(c_679, plain, (r2_hidden('#skF_4', '#skF_3') | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_674, c_560])).
% 3.57/1.56  tff(c_684, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_679])).
% 3.57/1.56  tff(c_114, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | ~r1_tarski(k1_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.57/1.56  tff(c_128, plain, (![A_41]: (r2_hidden(A_41, k1_tarski(A_41)))), inference(resolution, [status(thm)], [c_24, c_114])).
% 3.57/1.56  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.56  tff(c_686, plain, (![A_99, B_100, C_101]: (~r2_hidden('#skF_1'(A_99, B_100, C_101), B_100) | r2_hidden('#skF_2'(A_99, B_100, C_101), C_101) | k4_xboole_0(A_99, B_100)=C_101)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.56  tff(c_689, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_686])).
% 3.57/1.56  tff(c_720, plain, (![A_104, C_105]: (r2_hidden('#skF_2'(A_104, A_104, C_105), C_105) | k1_xboole_0=C_105)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_689])).
% 3.57/1.56  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.56  tff(c_1765, plain, (![A_149, A_150, B_151]: (r2_hidden('#skF_2'(A_149, A_149, k4_xboole_0(A_150, B_151)), A_150) | k4_xboole_0(A_150, B_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_720, c_6])).
% 3.57/1.56  tff(c_1846, plain, (![A_152, B_153]: ('#skF_2'(A_152, A_152, k4_xboole_0('#skF_3', B_153))='#skF_4' | k4_xboole_0('#skF_3', B_153)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1765, c_50])).
% 3.57/1.56  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.56  tff(c_772, plain, (![A_104, A_1, B_2]: (~r2_hidden('#skF_2'(A_104, A_104, k4_xboole_0(A_1, B_2)), B_2) | k4_xboole_0(A_1, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_720, c_4])).
% 3.57/1.56  tff(c_1901, plain, (![B_154]: (~r2_hidden('#skF_4', B_154) | k4_xboole_0('#skF_3', B_154)=k1_xboole_0 | k4_xboole_0('#skF_3', B_154)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1846, c_772])).
% 3.57/1.56  tff(c_1920, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_128, c_1901])).
% 3.57/1.56  tff(c_26, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.56  tff(c_309, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | k4_xboole_0(A_71, B_70)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_129])).
% 3.57/1.56  tff(c_322, plain, (![A_17, B_18]: (k1_tarski(A_17)=B_18 | k4_xboole_0(B_18, k1_tarski(A_17))!=k1_xboole_0 | ~r2_hidden(A_17, B_18))), inference(resolution, [status(thm)], [c_38, c_309])).
% 3.57/1.56  tff(c_1954, plain, (k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1920, c_322])).
% 3.57/1.56  tff(c_1987, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_684, c_1954])).
% 3.57/1.56  tff(c_1989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1987])).
% 3.57/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.56  
% 3.57/1.56  Inference rules
% 3.57/1.56  ----------------------
% 3.57/1.56  #Ref     : 0
% 3.57/1.56  #Sup     : 420
% 3.57/1.56  #Fact    : 0
% 3.57/1.56  #Define  : 0
% 3.57/1.56  #Split   : 0
% 3.57/1.56  #Chain   : 0
% 3.57/1.56  #Close   : 0
% 3.57/1.56  
% 3.57/1.56  Ordering : KBO
% 3.57/1.56  
% 3.57/1.56  Simplification rules
% 3.57/1.56  ----------------------
% 3.57/1.56  #Subsume      : 84
% 3.57/1.56  #Demod        : 124
% 3.57/1.56  #Tautology    : 184
% 3.57/1.56  #SimpNegUnit  : 96
% 3.57/1.56  #BackRed      : 2
% 3.57/1.56  
% 3.57/1.56  #Partial instantiations: 0
% 3.57/1.56  #Strategies tried      : 1
% 3.57/1.56  
% 3.57/1.56  Timing (in seconds)
% 3.57/1.56  ----------------------
% 3.57/1.57  Preprocessing        : 0.30
% 3.57/1.57  Parsing              : 0.16
% 3.57/1.57  CNF conversion       : 0.02
% 3.57/1.57  Main loop            : 0.50
% 3.57/1.57  Inferencing          : 0.18
% 3.57/1.57  Reduction            : 0.15
% 3.57/1.57  Demodulation         : 0.10
% 3.57/1.57  BG Simplification    : 0.03
% 3.57/1.57  Subsumption          : 0.11
% 3.57/1.57  Abstraction          : 0.03
% 3.57/1.57  MUC search           : 0.00
% 3.57/1.57  Cooper               : 0.00
% 3.57/1.57  Total                : 0.83
% 3.57/1.57  Index Insertion      : 0.00
% 3.57/1.57  Index Deletion       : 0.00
% 3.57/1.57  Index Matching       : 0.00
% 3.57/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
