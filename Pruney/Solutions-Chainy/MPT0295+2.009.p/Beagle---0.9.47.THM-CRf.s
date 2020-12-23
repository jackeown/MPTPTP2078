%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:37 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 186 expanded)
%              Number of equality atoms :    9 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_2 > #skF_7 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_56,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    r2_hidden('#skF_13','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ! [D_60,B_61,A_62] :
      ( ~ r2_hidden(D_60,B_61)
      | ~ r2_hidden(D_60,k4_xboole_0(A_62,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [A_82,A_83,B_84] :
      ( ~ r2_hidden('#skF_3'(A_82,k4_xboole_0(A_83,B_84)),B_84)
      | r1_xboole_0(A_82,k4_xboole_0(A_83,B_84)) ) ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_123,plain,(
    ! [A_85,A_86] : r1_xboole_0(A_85,k4_xboole_0(A_86,A_85)) ),
    inference(resolution,[status(thm)],[c_24,c_112])).

tff(c_26,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_131,plain,(
    ! [A_91,A_92,A_93] :
      ( r1_xboole_0(A_91,k4_xboole_0(A_92,A_93))
      | ~ r1_tarski(A_91,A_93) ) ),
    inference(resolution,[status(thm)],[c_123,c_26])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_164,plain,(
    ! [C_103,A_104,A_105,A_106] :
      ( ~ r2_hidden(C_103,k4_xboole_0(A_104,A_105))
      | ~ r2_hidden(C_103,A_106)
      | ~ r1_tarski(A_106,A_105) ) ),
    inference(resolution,[status(thm)],[c_131,c_20])).

tff(c_594,plain,(
    ! [D_191,A_192,B_193,A_194] :
      ( ~ r2_hidden(D_191,A_192)
      | ~ r1_tarski(A_192,B_193)
      | r2_hidden(D_191,B_193)
      | ~ r2_hidden(D_191,A_194) ) ),
    inference(resolution,[status(thm)],[c_2,c_164])).

tff(c_621,plain,(
    ! [B_193,A_194] :
      ( ~ r1_tarski('#skF_10',B_193)
      | r2_hidden('#skF_13',B_193)
      | ~ r2_hidden('#skF_13',A_194) ) ),
    inference(resolution,[status(thm)],[c_54,c_594])).

tff(c_622,plain,(
    ! [A_194] : ~ r2_hidden('#skF_13',A_194) ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_622,c_54])).

tff(c_708,plain,(
    ! [B_193] :
      ( ~ r1_tarski('#skF_10',B_193)
      | r2_hidden('#skF_13',B_193) ) ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_34,plain,(
    ! [A_15,B_16,D_42] :
      ( r2_hidden('#skF_8'(A_15,B_16,k2_zfmisc_1(A_15,B_16),D_42),A_15)
      | ~ r2_hidden(D_42,k2_zfmisc_1(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_15,B_16,D_42] :
      ( r2_hidden('#skF_9'(A_15,B_16,k2_zfmisc_1(A_15,B_16),D_42),B_16)
      | ~ r2_hidden(D_42,k2_zfmisc_1(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1660,plain,(
    ! [A_348,B_349,D_350] :
      ( k4_tarski('#skF_8'(A_348,B_349,k2_zfmisc_1(A_348,B_349),D_350),'#skF_9'(A_348,B_349,k2_zfmisc_1(A_348,B_349),D_350)) = D_350
      | ~ r2_hidden(D_350,k2_zfmisc_1(A_348,B_349)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ! [E_51,F_52] :
      ( k4_tarski(E_51,F_52) != '#skF_13'
      | ~ r2_hidden(F_52,'#skF_12')
      | ~ r2_hidden(E_51,'#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1679,plain,(
    ! [D_356,A_357,B_358] :
      ( D_356 != '#skF_13'
      | ~ r2_hidden('#skF_9'(A_357,B_358,k2_zfmisc_1(A_357,B_358),D_356),'#skF_12')
      | ~ r2_hidden('#skF_8'(A_357,B_358,k2_zfmisc_1(A_357,B_358),D_356),'#skF_11')
      | ~ r2_hidden(D_356,k2_zfmisc_1(A_357,B_358)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1660,c_52])).

tff(c_1794,plain,(
    ! [D_379,A_380] :
      ( D_379 != '#skF_13'
      | ~ r2_hidden('#skF_8'(A_380,'#skF_12',k2_zfmisc_1(A_380,'#skF_12'),D_379),'#skF_11')
      | ~ r2_hidden(D_379,k2_zfmisc_1(A_380,'#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_32,c_1679])).

tff(c_1801,plain,(
    ! [D_381] :
      ( D_381 != '#skF_13'
      | ~ r2_hidden(D_381,k2_zfmisc_1('#skF_11','#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_34,c_1794])).

tff(c_1841,plain,(
    ~ r1_tarski('#skF_10',k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(resolution,[status(thm)],[c_708,c_1801])).

tff(c_1882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.67  
% 3.96/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_2 > #skF_7 > #skF_12
% 3.96/1.68  
% 3.96/1.68  %Foreground sorts:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Background operators:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Foreground operators:
% 3.96/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.68  tff('#skF_11', type, '#skF_11': $i).
% 3.96/1.68  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.96/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.96/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.96/1.68  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 3.96/1.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.96/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.96/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.68  tff('#skF_10', type, '#skF_10': $i).
% 3.96/1.68  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.96/1.68  tff('#skF_13', type, '#skF_13': $i).
% 3.96/1.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.96/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.96/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.96/1.68  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.68  tff('#skF_12', type, '#skF_12': $i).
% 3.96/1.68  
% 4.11/1.69  tff(f_85, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 4.11/1.69  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.11/1.69  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.11/1.69  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.11/1.69  tff(f_71, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 4.11/1.69  tff(c_56, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.11/1.69  tff(c_54, plain, (r2_hidden('#skF_13', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.11/1.69  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.11/1.69  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.11/1.69  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.11/1.69  tff(c_70, plain, (![D_60, B_61, A_62]: (~r2_hidden(D_60, B_61) | ~r2_hidden(D_60, k4_xboole_0(A_62, B_61)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.11/1.69  tff(c_112, plain, (![A_82, A_83, B_84]: (~r2_hidden('#skF_3'(A_82, k4_xboole_0(A_83, B_84)), B_84) | r1_xboole_0(A_82, k4_xboole_0(A_83, B_84)))), inference(resolution, [status(thm)], [c_22, c_70])).
% 4.11/1.69  tff(c_123, plain, (![A_85, A_86]: (r1_xboole_0(A_85, k4_xboole_0(A_86, A_85)))), inference(resolution, [status(thm)], [c_24, c_112])).
% 4.11/1.69  tff(c_26, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.11/1.69  tff(c_131, plain, (![A_91, A_92, A_93]: (r1_xboole_0(A_91, k4_xboole_0(A_92, A_93)) | ~r1_tarski(A_91, A_93))), inference(resolution, [status(thm)], [c_123, c_26])).
% 4.11/1.69  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.11/1.69  tff(c_164, plain, (![C_103, A_104, A_105, A_106]: (~r2_hidden(C_103, k4_xboole_0(A_104, A_105)) | ~r2_hidden(C_103, A_106) | ~r1_tarski(A_106, A_105))), inference(resolution, [status(thm)], [c_131, c_20])).
% 4.11/1.69  tff(c_594, plain, (![D_191, A_192, B_193, A_194]: (~r2_hidden(D_191, A_192) | ~r1_tarski(A_192, B_193) | r2_hidden(D_191, B_193) | ~r2_hidden(D_191, A_194))), inference(resolution, [status(thm)], [c_2, c_164])).
% 4.11/1.69  tff(c_621, plain, (![B_193, A_194]: (~r1_tarski('#skF_10', B_193) | r2_hidden('#skF_13', B_193) | ~r2_hidden('#skF_13', A_194))), inference(resolution, [status(thm)], [c_54, c_594])).
% 4.11/1.69  tff(c_622, plain, (![A_194]: (~r2_hidden('#skF_13', A_194))), inference(splitLeft, [status(thm)], [c_621])).
% 4.11/1.69  tff(c_707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_622, c_54])).
% 4.11/1.69  tff(c_708, plain, (![B_193]: (~r1_tarski('#skF_10', B_193) | r2_hidden('#skF_13', B_193))), inference(splitRight, [status(thm)], [c_621])).
% 4.11/1.69  tff(c_34, plain, (![A_15, B_16, D_42]: (r2_hidden('#skF_8'(A_15, B_16, k2_zfmisc_1(A_15, B_16), D_42), A_15) | ~r2_hidden(D_42, k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.11/1.69  tff(c_32, plain, (![A_15, B_16, D_42]: (r2_hidden('#skF_9'(A_15, B_16, k2_zfmisc_1(A_15, B_16), D_42), B_16) | ~r2_hidden(D_42, k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.11/1.69  tff(c_1660, plain, (![A_348, B_349, D_350]: (k4_tarski('#skF_8'(A_348, B_349, k2_zfmisc_1(A_348, B_349), D_350), '#skF_9'(A_348, B_349, k2_zfmisc_1(A_348, B_349), D_350))=D_350 | ~r2_hidden(D_350, k2_zfmisc_1(A_348, B_349)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.11/1.69  tff(c_52, plain, (![E_51, F_52]: (k4_tarski(E_51, F_52)!='#skF_13' | ~r2_hidden(F_52, '#skF_12') | ~r2_hidden(E_51, '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.11/1.69  tff(c_1679, plain, (![D_356, A_357, B_358]: (D_356!='#skF_13' | ~r2_hidden('#skF_9'(A_357, B_358, k2_zfmisc_1(A_357, B_358), D_356), '#skF_12') | ~r2_hidden('#skF_8'(A_357, B_358, k2_zfmisc_1(A_357, B_358), D_356), '#skF_11') | ~r2_hidden(D_356, k2_zfmisc_1(A_357, B_358)))), inference(superposition, [status(thm), theory('equality')], [c_1660, c_52])).
% 4.11/1.69  tff(c_1794, plain, (![D_379, A_380]: (D_379!='#skF_13' | ~r2_hidden('#skF_8'(A_380, '#skF_12', k2_zfmisc_1(A_380, '#skF_12'), D_379), '#skF_11') | ~r2_hidden(D_379, k2_zfmisc_1(A_380, '#skF_12')))), inference(resolution, [status(thm)], [c_32, c_1679])).
% 4.11/1.69  tff(c_1801, plain, (![D_381]: (D_381!='#skF_13' | ~r2_hidden(D_381, k2_zfmisc_1('#skF_11', '#skF_12')))), inference(resolution, [status(thm)], [c_34, c_1794])).
% 4.11/1.69  tff(c_1841, plain, (~r1_tarski('#skF_10', k2_zfmisc_1('#skF_11', '#skF_12'))), inference(resolution, [status(thm)], [c_708, c_1801])).
% 4.11/1.69  tff(c_1882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1841])).
% 4.11/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.69  
% 4.11/1.69  Inference rules
% 4.11/1.69  ----------------------
% 4.11/1.69  #Ref     : 0
% 4.11/1.69  #Sup     : 414
% 4.11/1.69  #Fact    : 0
% 4.11/1.69  #Define  : 0
% 4.11/1.69  #Split   : 7
% 4.11/1.69  #Chain   : 0
% 4.11/1.69  #Close   : 0
% 4.11/1.69  
% 4.11/1.69  Ordering : KBO
% 4.11/1.69  
% 4.11/1.69  Simplification rules
% 4.11/1.69  ----------------------
% 4.11/1.69  #Subsume      : 57
% 4.11/1.69  #Demod        : 29
% 4.11/1.69  #Tautology    : 36
% 4.11/1.69  #SimpNegUnit  : 12
% 4.11/1.69  #BackRed      : 12
% 4.11/1.69  
% 4.11/1.69  #Partial instantiations: 0
% 4.11/1.69  #Strategies tried      : 1
% 4.11/1.69  
% 4.11/1.69  Timing (in seconds)
% 4.11/1.69  ----------------------
% 4.11/1.69  Preprocessing        : 0.29
% 4.11/1.69  Parsing              : 0.14
% 4.11/1.69  CNF conversion       : 0.03
% 4.11/1.69  Main loop            : 0.64
% 4.11/1.69  Inferencing          : 0.22
% 4.11/1.69  Reduction            : 0.15
% 4.11/1.69  Demodulation         : 0.11
% 4.11/1.69  BG Simplification    : 0.03
% 4.11/1.69  Subsumption          : 0.18
% 4.11/1.69  Abstraction          : 0.03
% 4.11/1.69  MUC search           : 0.00
% 4.11/1.69  Cooper               : 0.00
% 4.11/1.69  Total                : 0.95
% 4.11/1.69  Index Insertion      : 0.00
% 4.11/1.69  Index Deletion       : 0.00
% 4.11/1.69  Index Matching       : 0.00
% 4.11/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
