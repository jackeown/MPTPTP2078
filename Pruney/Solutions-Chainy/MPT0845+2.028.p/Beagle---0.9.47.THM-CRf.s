%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:48 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 (  92 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_607,plain,(
    ! [A_1928,B_1929,C_1930] :
      ( r2_hidden('#skF_1'(A_1928,B_1929,C_1930),B_1929)
      | r2_hidden('#skF_2'(A_1928,B_1929,C_1930),C_1930)
      | k3_xboole_0(A_1928,B_1929) = C_1930 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,(
    ! [D_63,A_64,B_65] :
      ( r2_hidden(D_63,A_64)
      | ~ r2_hidden(D_63,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [D_63,A_12] :
      ( r2_hidden(D_63,A_12)
      | ~ r2_hidden(D_63,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_93])).

tff(c_625,plain,(
    ! [A_1928,C_1930,A_12] :
      ( r2_hidden('#skF_1'(A_1928,k1_xboole_0,C_1930),A_12)
      | r2_hidden('#skF_2'(A_1928,k1_xboole_0,C_1930),C_1930)
      | k3_xboole_0(A_1928,k1_xboole_0) = C_1930 ) ),
    inference(resolution,[status(thm)],[c_607,c_108])).

tff(c_1231,plain,(
    ! [A_1990,C_1991,A_1992] :
      ( r2_hidden('#skF_1'(A_1990,k1_xboole_0,C_1991),A_1992)
      | r2_hidden('#skF_2'(A_1990,k1_xboole_0,C_1991),C_1991)
      | k1_xboole_0 = C_1991 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_625])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1235,plain,(
    ! [A_1990,A_1992] :
      ( k3_xboole_0(A_1990,k1_xboole_0) = A_1992
      | r2_hidden('#skF_2'(A_1990,k1_xboole_0,A_1992),A_1992)
      | k1_xboole_0 = A_1992 ) ),
    inference(resolution,[status(thm)],[c_1231,c_14])).

tff(c_1276,plain,(
    ! [A_1992,A_1990] :
      ( k1_xboole_0 = A_1992
      | r2_hidden('#skF_2'(A_1990,k1_xboole_0,A_1992),A_1992)
      | k1_xboole_0 = A_1992 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1235])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_241,plain,(
    ! [D_96,A_97,B_98] :
      ( ~ r2_hidden(D_96,'#skF_4'(A_97,B_98))
      | ~ r2_hidden(D_96,B_98)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1500,plain,(
    ! [A_2014,B_2015,B_2016] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_2014,B_2015),B_2016),B_2015)
      | ~ r2_hidden(A_2014,B_2015)
      | r1_xboole_0('#skF_4'(A_2014,B_2015),B_2016) ) ),
    inference(resolution,[status(thm)],[c_24,c_241])).

tff(c_1521,plain,(
    ! [A_2017,B_2018] :
      ( ~ r2_hidden(A_2017,B_2018)
      | r1_xboole_0('#skF_4'(A_2017,B_2018),B_2018) ) ),
    inference(resolution,[status(thm)],[c_22,c_1500])).

tff(c_75,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_4'(A_57,B_58),B_58)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [B_50] :
      ( ~ r1_xboole_0(B_50,'#skF_5')
      | ~ r2_hidden(B_50,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_80,plain,(
    ! [A_57] :
      ( ~ r1_xboole_0('#skF_4'(A_57,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_57,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_75,c_46])).

tff(c_1580,plain,(
    ! [A_2022] : ~ r2_hidden(A_2022,'#skF_5') ),
    inference(resolution,[status(thm)],[c_1521,c_80])).

tff(c_1596,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1276,c_1580])).

tff(c_1677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_1596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.57  
% 3.40/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.57  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.40/1.57  
% 3.40/1.57  %Foreground sorts:
% 3.40/1.57  
% 3.40/1.57  
% 3.40/1.57  %Background operators:
% 3.40/1.57  
% 3.40/1.57  
% 3.40/1.57  %Foreground operators:
% 3.40/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.40/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.40/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.40/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.40/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.40/1.57  
% 3.40/1.58  tff(f_92, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.40/1.58  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.40/1.58  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.40/1.58  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.40/1.58  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 3.40/1.58  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.40/1.58  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.40/1.58  tff(c_607, plain, (![A_1928, B_1929, C_1930]: (r2_hidden('#skF_1'(A_1928, B_1929, C_1930), B_1929) | r2_hidden('#skF_2'(A_1928, B_1929, C_1930), C_1930) | k3_xboole_0(A_1928, B_1929)=C_1930)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.58  tff(c_93, plain, (![D_63, A_64, B_65]: (r2_hidden(D_63, A_64) | ~r2_hidden(D_63, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.58  tff(c_108, plain, (![D_63, A_12]: (r2_hidden(D_63, A_12) | ~r2_hidden(D_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_93])).
% 3.40/1.58  tff(c_625, plain, (![A_1928, C_1930, A_12]: (r2_hidden('#skF_1'(A_1928, k1_xboole_0, C_1930), A_12) | r2_hidden('#skF_2'(A_1928, k1_xboole_0, C_1930), C_1930) | k3_xboole_0(A_1928, k1_xboole_0)=C_1930)), inference(resolution, [status(thm)], [c_607, c_108])).
% 3.40/1.58  tff(c_1231, plain, (![A_1990, C_1991, A_1992]: (r2_hidden('#skF_1'(A_1990, k1_xboole_0, C_1991), A_1992) | r2_hidden('#skF_2'(A_1990, k1_xboole_0, C_1991), C_1991) | k1_xboole_0=C_1991)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_625])).
% 3.40/1.58  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.58  tff(c_1235, plain, (![A_1990, A_1992]: (k3_xboole_0(A_1990, k1_xboole_0)=A_1992 | r2_hidden('#skF_2'(A_1990, k1_xboole_0, A_1992), A_1992) | k1_xboole_0=A_1992)), inference(resolution, [status(thm)], [c_1231, c_14])).
% 3.40/1.58  tff(c_1276, plain, (![A_1992, A_1990]: (k1_xboole_0=A_1992 | r2_hidden('#skF_2'(A_1990, k1_xboole_0, A_1992), A_1992) | k1_xboole_0=A_1992)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1235])).
% 3.40/1.58  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.58  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.58  tff(c_241, plain, (![D_96, A_97, B_98]: (~r2_hidden(D_96, '#skF_4'(A_97, B_98)) | ~r2_hidden(D_96, B_98) | ~r2_hidden(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.58  tff(c_1500, plain, (![A_2014, B_2015, B_2016]: (~r2_hidden('#skF_3'('#skF_4'(A_2014, B_2015), B_2016), B_2015) | ~r2_hidden(A_2014, B_2015) | r1_xboole_0('#skF_4'(A_2014, B_2015), B_2016))), inference(resolution, [status(thm)], [c_24, c_241])).
% 3.40/1.58  tff(c_1521, plain, (![A_2017, B_2018]: (~r2_hidden(A_2017, B_2018) | r1_xboole_0('#skF_4'(A_2017, B_2018), B_2018))), inference(resolution, [status(thm)], [c_22, c_1500])).
% 3.40/1.58  tff(c_75, plain, (![A_57, B_58]: (r2_hidden('#skF_4'(A_57, B_58), B_58) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.58  tff(c_46, plain, (![B_50]: (~r1_xboole_0(B_50, '#skF_5') | ~r2_hidden(B_50, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.40/1.58  tff(c_80, plain, (![A_57]: (~r1_xboole_0('#skF_4'(A_57, '#skF_5'), '#skF_5') | ~r2_hidden(A_57, '#skF_5'))), inference(resolution, [status(thm)], [c_75, c_46])).
% 3.40/1.58  tff(c_1580, plain, (![A_2022]: (~r2_hidden(A_2022, '#skF_5'))), inference(resolution, [status(thm)], [c_1521, c_80])).
% 3.40/1.58  tff(c_1596, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1276, c_1580])).
% 3.40/1.58  tff(c_1677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_1596])).
% 3.40/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.58  
% 3.40/1.58  Inference rules
% 3.40/1.58  ----------------------
% 3.40/1.58  #Ref     : 0
% 3.40/1.58  #Sup     : 339
% 3.40/1.58  #Fact    : 0
% 3.40/1.58  #Define  : 0
% 3.40/1.58  #Split   : 1
% 3.40/1.58  #Chain   : 0
% 3.40/1.58  #Close   : 0
% 3.40/1.58  
% 3.40/1.58  Ordering : KBO
% 3.40/1.58  
% 3.40/1.58  Simplification rules
% 3.40/1.58  ----------------------
% 3.40/1.58  #Subsume      : 95
% 3.40/1.58  #Demod        : 138
% 3.40/1.58  #Tautology    : 93
% 3.40/1.58  #SimpNegUnit  : 16
% 3.40/1.58  #BackRed      : 4
% 3.40/1.58  
% 3.40/1.58  #Partial instantiations: 192
% 3.40/1.58  #Strategies tried      : 1
% 3.40/1.58  
% 3.40/1.58  Timing (in seconds)
% 3.40/1.58  ----------------------
% 3.40/1.58  Preprocessing        : 0.33
% 3.40/1.58  Parsing              : 0.17
% 3.40/1.58  CNF conversion       : 0.03
% 3.40/1.58  Main loop            : 0.50
% 3.40/1.58  Inferencing          : 0.21
% 3.40/1.58  Reduction            : 0.12
% 3.40/1.58  Demodulation         : 0.08
% 3.40/1.58  BG Simplification    : 0.03
% 3.40/1.58  Subsumption          : 0.10
% 3.40/1.58  Abstraction          : 0.02
% 3.40/1.58  MUC search           : 0.00
% 3.40/1.58  Cooper               : 0.00
% 3.40/1.58  Total                : 0.85
% 3.40/1.58  Index Insertion      : 0.00
% 3.40/1.58  Index Deletion       : 0.00
% 3.40/1.58  Index Matching       : 0.00
% 3.40/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
