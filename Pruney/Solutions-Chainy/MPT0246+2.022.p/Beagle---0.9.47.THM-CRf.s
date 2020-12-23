%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:02 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 120 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_40,plain,(
    k1_tarski('#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [C_38,B_37] : r1_tarski(k1_tarski(C_38),k2_tarski(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_65,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | ~ r1_tarski(k1_tarski(A_51),B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [C_38,B_37] : r2_hidden(C_38,k2_tarski(B_37,C_38)) ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_194,plain,(
    ! [A_91,B_92,B_93] :
      ( r2_hidden('#skF_1'(A_91,B_92),B_93)
      | ~ r1_tarski(A_91,B_93)
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_36,plain,(
    ! [C_40] :
      ( C_40 = '#skF_3'
      | ~ r2_hidden(C_40,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_208,plain,(
    ! [A_94,B_95] :
      ( '#skF_1'(A_94,B_95) = '#skF_3'
      | ~ r1_tarski(A_94,'#skF_2')
      | r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_194,c_36])).

tff(c_221,plain,(
    ! [A_96,B_97] :
      ( '#skF_1'(k1_tarski(A_96),B_97) = '#skF_3'
      | r1_tarski(k1_tarski(A_96),B_97)
      | ~ r2_hidden(A_96,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_208])).

tff(c_22,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | ~ r1_tarski(k1_tarski(A_34),B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_230,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(A_98,B_99)
      | '#skF_1'(k1_tarski(A_98),B_99) = '#skF_3'
      | ~ r2_hidden(A_98,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_221,c_22])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_248,plain,(
    ! [B_100,A_101] :
      ( ~ r2_hidden('#skF_3',B_100)
      | r1_tarski(k1_tarski(A_101),B_100)
      | r2_hidden(A_101,B_100)
      | ~ r2_hidden(A_101,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_4])).

tff(c_257,plain,(
    ! [B_102,A_103] :
      ( ~ r2_hidden('#skF_3',B_102)
      | r2_hidden(A_103,B_102)
      | ~ r2_hidden(A_103,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_248,c_22])).

tff(c_283,plain,(
    ! [A_105,B_106] :
      ( r2_hidden(A_105,k2_tarski(B_106,'#skF_3'))
      | ~ r2_hidden(A_105,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_77,c_257])).

tff(c_573,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(A_144,k2_tarski(B_145,'#skF_3'))
      | ~ r2_hidden('#skF_1'(A_144,k2_tarski(B_145,'#skF_3')),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_283,c_4])).

tff(c_607,plain,(
    ! [B_153] : r1_tarski('#skF_2',k2_tarski(B_153,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_573])).

tff(c_26,plain,(
    ! [B_37,C_38,A_36] :
      ( k2_tarski(B_37,C_38) = A_36
      | k1_tarski(C_38) = A_36
      | k1_tarski(B_37) = A_36
      | k1_xboole_0 = A_36
      | ~ r1_tarski(A_36,k2_tarski(B_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_610,plain,(
    ! [B_153] :
      ( k2_tarski(B_153,'#skF_3') = '#skF_2'
      | k1_tarski('#skF_3') = '#skF_2'
      | k1_tarski(B_153) = '#skF_2'
      | k1_xboole_0 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_607,c_26])).

tff(c_619,plain,(
    ! [B_154] :
      ( k2_tarski(B_154,'#skF_3') = '#skF_2'
      | k1_tarski(B_154) = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_40,c_610])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_675,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_tarski('#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_8])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:41:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.30  
% 2.35/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.30  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.71/1.30  
% 2.71/1.30  %Foreground sorts:
% 2.71/1.30  
% 2.71/1.30  
% 2.71/1.30  %Background operators:
% 2.71/1.30  
% 2.71/1.30  
% 2.71/1.30  %Foreground operators:
% 2.71/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.30  
% 2.71/1.31  tff(f_80, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.71/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.71/1.31  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.71/1.31  tff(f_50, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.71/1.31  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.71/1.31  tff(c_40, plain, (k1_tarski('#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.31  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.31  tff(c_30, plain, (![C_38, B_37]: (r1_tarski(k1_tarski(C_38), k2_tarski(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.31  tff(c_65, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | ~r1_tarski(k1_tarski(A_51), B_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.31  tff(c_77, plain, (![C_38, B_37]: (r2_hidden(C_38, k2_tarski(B_37, C_38)))), inference(resolution, [status(thm)], [c_30, c_65])).
% 2.71/1.31  tff(c_24, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.31  tff(c_143, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.31  tff(c_194, plain, (![A_91, B_92, B_93]: (r2_hidden('#skF_1'(A_91, B_92), B_93) | ~r1_tarski(A_91, B_93) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_6, c_143])).
% 2.71/1.31  tff(c_36, plain, (![C_40]: (C_40='#skF_3' | ~r2_hidden(C_40, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.31  tff(c_208, plain, (![A_94, B_95]: ('#skF_1'(A_94, B_95)='#skF_3' | ~r1_tarski(A_94, '#skF_2') | r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_194, c_36])).
% 2.71/1.31  tff(c_221, plain, (![A_96, B_97]: ('#skF_1'(k1_tarski(A_96), B_97)='#skF_3' | r1_tarski(k1_tarski(A_96), B_97) | ~r2_hidden(A_96, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_208])).
% 2.71/1.31  tff(c_22, plain, (![A_34, B_35]: (r2_hidden(A_34, B_35) | ~r1_tarski(k1_tarski(A_34), B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.31  tff(c_230, plain, (![A_98, B_99]: (r2_hidden(A_98, B_99) | '#skF_1'(k1_tarski(A_98), B_99)='#skF_3' | ~r2_hidden(A_98, '#skF_2'))), inference(resolution, [status(thm)], [c_221, c_22])).
% 2.71/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.31  tff(c_248, plain, (![B_100, A_101]: (~r2_hidden('#skF_3', B_100) | r1_tarski(k1_tarski(A_101), B_100) | r2_hidden(A_101, B_100) | ~r2_hidden(A_101, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_4])).
% 2.71/1.31  tff(c_257, plain, (![B_102, A_103]: (~r2_hidden('#skF_3', B_102) | r2_hidden(A_103, B_102) | ~r2_hidden(A_103, '#skF_2'))), inference(resolution, [status(thm)], [c_248, c_22])).
% 2.71/1.31  tff(c_283, plain, (![A_105, B_106]: (r2_hidden(A_105, k2_tarski(B_106, '#skF_3')) | ~r2_hidden(A_105, '#skF_2'))), inference(resolution, [status(thm)], [c_77, c_257])).
% 2.71/1.31  tff(c_573, plain, (![A_144, B_145]: (r1_tarski(A_144, k2_tarski(B_145, '#skF_3')) | ~r2_hidden('#skF_1'(A_144, k2_tarski(B_145, '#skF_3')), '#skF_2'))), inference(resolution, [status(thm)], [c_283, c_4])).
% 2.71/1.31  tff(c_607, plain, (![B_153]: (r1_tarski('#skF_2', k2_tarski(B_153, '#skF_3')))), inference(resolution, [status(thm)], [c_6, c_573])).
% 2.71/1.31  tff(c_26, plain, (![B_37, C_38, A_36]: (k2_tarski(B_37, C_38)=A_36 | k1_tarski(C_38)=A_36 | k1_tarski(B_37)=A_36 | k1_xboole_0=A_36 | ~r1_tarski(A_36, k2_tarski(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.31  tff(c_610, plain, (![B_153]: (k2_tarski(B_153, '#skF_3')='#skF_2' | k1_tarski('#skF_3')='#skF_2' | k1_tarski(B_153)='#skF_2' | k1_xboole_0='#skF_2')), inference(resolution, [status(thm)], [c_607, c_26])).
% 2.71/1.31  tff(c_619, plain, (![B_154]: (k2_tarski(B_154, '#skF_3')='#skF_2' | k1_tarski(B_154)='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_40, c_610])).
% 2.71/1.31  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.71/1.31  tff(c_675, plain, (k1_tarski('#skF_3')='#skF_2' | k1_tarski('#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_619, c_8])).
% 2.71/1.31  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_675])).
% 2.71/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.31  
% 2.71/1.31  Inference rules
% 2.71/1.31  ----------------------
% 2.71/1.31  #Ref     : 0
% 2.71/1.31  #Sup     : 151
% 2.71/1.31  #Fact    : 0
% 2.71/1.31  #Define  : 0
% 2.71/1.31  #Split   : 1
% 2.71/1.31  #Chain   : 0
% 2.71/1.31  #Close   : 0
% 2.71/1.31  
% 2.71/1.31  Ordering : KBO
% 2.71/1.31  
% 2.71/1.31  Simplification rules
% 2.71/1.31  ----------------------
% 2.71/1.31  #Subsume      : 48
% 2.71/1.31  #Demod        : 20
% 2.71/1.31  #Tautology    : 40
% 2.71/1.31  #SimpNegUnit  : 10
% 2.71/1.31  #BackRed      : 0
% 2.71/1.31  
% 2.71/1.31  #Partial instantiations: 0
% 2.71/1.31  #Strategies tried      : 1
% 2.71/1.31  
% 2.71/1.31  Timing (in seconds)
% 2.71/1.31  ----------------------
% 2.71/1.32  Preprocessing        : 0.29
% 2.71/1.32  Parsing              : 0.15
% 2.71/1.32  CNF conversion       : 0.02
% 2.71/1.32  Main loop            : 0.33
% 2.71/1.32  Inferencing          : 0.13
% 2.71/1.32  Reduction            : 0.09
% 2.71/1.32  Demodulation         : 0.07
% 2.71/1.32  BG Simplification    : 0.02
% 2.71/1.32  Subsumption          : 0.07
% 2.71/1.32  Abstraction          : 0.01
% 2.71/1.32  MUC search           : 0.00
% 2.71/1.32  Cooper               : 0.00
% 2.71/1.32  Total                : 0.64
% 2.71/1.32  Index Insertion      : 0.00
% 2.71/1.32  Index Deletion       : 0.00
% 2.71/1.32  Index Matching       : 0.00
% 2.71/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
