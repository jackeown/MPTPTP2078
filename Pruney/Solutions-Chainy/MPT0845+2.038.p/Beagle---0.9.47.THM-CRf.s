%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:49 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   52 (  80 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 179 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

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

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_764,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r2_hidden('#skF_1'(A_111,B_112,C_113),C_113)
      | r2_hidden('#skF_2'(A_111,B_112,C_113),C_113)
      | k4_xboole_0(A_111,B_112) = C_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_773,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_764])).

tff(c_814,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_2'(A_118,B_119,A_118),A_118)
      | k4_xboole_0(A_118,B_119) = A_118 ) ),
    inference(resolution,[status(thm)],[c_18,c_764])).

tff(c_26,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_49,plain,(
    ! [D_27,B_28,A_29] :
      ( ~ r2_hidden(D_27,B_28)
      | ~ r2_hidden(D_27,k4_xboole_0(A_29,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [D_27,A_12] :
      ( ~ r2_hidden(D_27,k1_xboole_0)
      | ~ r2_hidden(D_27,A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_49])).

tff(c_849,plain,(
    ! [B_120,A_121] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_120,k1_xboole_0),A_121)
      | k4_xboole_0(k1_xboole_0,B_120) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_814,c_52])).

tff(c_864,plain,(
    ! [B_2] : k4_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_773,c_849])).

tff(c_417,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden('#skF_1'(A_91,B_92,C_93),A_91)
      | r2_hidden('#skF_2'(A_91,B_92,C_93),C_93)
      | k4_xboole_0(A_91,B_92) = C_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_462,plain,(
    ! [A_91,C_93] :
      ( r2_hidden('#skF_2'(A_91,A_91,C_93),C_93)
      | k4_xboole_0(A_91,A_91) = C_93 ) ),
    inference(resolution,[status(thm)],[c_417,c_16])).

tff(c_568,plain,(
    ! [A_102,C_103] :
      ( r2_hidden('#skF_2'(A_102,A_102,C_103),C_103)
      | k4_xboole_0(A_102,A_102) = C_103 ) ),
    inference(resolution,[status(thm)],[c_417,c_16])).

tff(c_601,plain,(
    ! [A_104,A_105] :
      ( ~ r2_hidden('#skF_2'(A_104,A_104,k1_xboole_0),A_105)
      | k4_xboole_0(A_104,A_104) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_568,c_52])).

tff(c_612,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_462,c_601])).

tff(c_53,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_4'(A_30,B_31),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_30,A_1,B_2] :
      ( r2_hidden('#skF_4'(A_30,k4_xboole_0(A_1,B_2)),A_1)
      | ~ r2_hidden(A_30,k4_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_53,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1014,plain,(
    ! [A_133,A_134,B_135] :
      ( ~ r2_hidden('#skF_4'(A_133,k4_xboole_0(A_134,B_135)),B_135)
      | ~ r2_hidden(A_133,k4_xboole_0(A_134,B_135)) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_1024,plain,(
    ! [A_30,A_1] : ~ r2_hidden(A_30,k4_xboole_0(A_1,A_1)) ),
    inference(resolution,[status(thm)],[c_67,c_1014])).

tff(c_1038,plain,(
    ! [A_136] : ~ r2_hidden(A_136,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_1024])).

tff(c_1050,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2,C_3),C_3)
      | k4_xboole_0(k1_xboole_0,B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_1038])).

tff(c_1082,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2,C_3),C_3)
      | k1_xboole_0 = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_1050])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_157,plain,(
    ! [D_52,A_53,B_54] :
      ( ~ r2_hidden(D_52,'#skF_4'(A_53,B_54))
      | ~ r2_hidden(D_52,B_54)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1857,plain,(
    ! [A_189,B_190,B_191] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_189,B_190),B_191),B_190)
      | ~ r2_hidden(A_189,B_190)
      | r1_xboole_0('#skF_4'(A_189,B_190),B_191) ) ),
    inference(resolution,[status(thm)],[c_24,c_157])).

tff(c_1875,plain,(
    ! [A_192,B_193] :
      ( ~ r2_hidden(A_192,B_193)
      | r1_xboole_0('#skF_4'(A_192,B_193),B_193) ) ),
    inference(resolution,[status(thm)],[c_22,c_1857])).

tff(c_32,plain,(
    ! [B_21] :
      ( ~ r1_xboole_0(B_21,'#skF_5')
      | ~ r2_hidden(B_21,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    ! [A_30] :
      ( ~ r1_xboole_0('#skF_4'(A_30,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_30,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_53,c_32])).

tff(c_1906,plain,(
    ! [A_196] : ~ r2_hidden(A_196,'#skF_5') ),
    inference(resolution,[status(thm)],[c_1875,c_68])).

tff(c_1928,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1082,c_1906])).

tff(c_1974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1928])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:31:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.53  
% 3.37/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.53  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.37/1.53  
% 3.37/1.53  %Foreground sorts:
% 3.37/1.53  
% 3.37/1.53  
% 3.37/1.53  %Background operators:
% 3.37/1.53  
% 3.37/1.53  
% 3.37/1.53  %Foreground operators:
% 3.37/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.37/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.37/1.53  
% 3.37/1.55  tff(f_79, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.37/1.55  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.37/1.55  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.37/1.55  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 3.37/1.55  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.37/1.55  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.37/1.55  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.55  tff(c_764, plain, (![A_111, B_112, C_113]: (~r2_hidden('#skF_1'(A_111, B_112, C_113), C_113) | r2_hidden('#skF_2'(A_111, B_112, C_113), C_113) | k4_xboole_0(A_111, B_112)=C_113)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.55  tff(c_773, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_764])).
% 3.37/1.55  tff(c_814, plain, (![A_118, B_119]: (r2_hidden('#skF_2'(A_118, B_119, A_118), A_118) | k4_xboole_0(A_118, B_119)=A_118)), inference(resolution, [status(thm)], [c_18, c_764])).
% 3.37/1.55  tff(c_26, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.37/1.55  tff(c_49, plain, (![D_27, B_28, A_29]: (~r2_hidden(D_27, B_28) | ~r2_hidden(D_27, k4_xboole_0(A_29, B_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.55  tff(c_52, plain, (![D_27, A_12]: (~r2_hidden(D_27, k1_xboole_0) | ~r2_hidden(D_27, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_49])).
% 3.37/1.55  tff(c_849, plain, (![B_120, A_121]: (~r2_hidden('#skF_2'(k1_xboole_0, B_120, k1_xboole_0), A_121) | k4_xboole_0(k1_xboole_0, B_120)=k1_xboole_0)), inference(resolution, [status(thm)], [c_814, c_52])).
% 3.37/1.55  tff(c_864, plain, (![B_2]: (k4_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_773, c_849])).
% 3.37/1.55  tff(c_417, plain, (![A_91, B_92, C_93]: (r2_hidden('#skF_1'(A_91, B_92, C_93), A_91) | r2_hidden('#skF_2'(A_91, B_92, C_93), C_93) | k4_xboole_0(A_91, B_92)=C_93)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.55  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.55  tff(c_462, plain, (![A_91, C_93]: (r2_hidden('#skF_2'(A_91, A_91, C_93), C_93) | k4_xboole_0(A_91, A_91)=C_93)), inference(resolution, [status(thm)], [c_417, c_16])).
% 3.37/1.55  tff(c_568, plain, (![A_102, C_103]: (r2_hidden('#skF_2'(A_102, A_102, C_103), C_103) | k4_xboole_0(A_102, A_102)=C_103)), inference(resolution, [status(thm)], [c_417, c_16])).
% 3.37/1.55  tff(c_601, plain, (![A_104, A_105]: (~r2_hidden('#skF_2'(A_104, A_104, k1_xboole_0), A_105) | k4_xboole_0(A_104, A_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_568, c_52])).
% 3.37/1.55  tff(c_612, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_462, c_601])).
% 3.37/1.55  tff(c_53, plain, (![A_30, B_31]: (r2_hidden('#skF_4'(A_30, B_31), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.55  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.55  tff(c_67, plain, (![A_30, A_1, B_2]: (r2_hidden('#skF_4'(A_30, k4_xboole_0(A_1, B_2)), A_1) | ~r2_hidden(A_30, k4_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_53, c_6])).
% 3.37/1.55  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.55  tff(c_1014, plain, (![A_133, A_134, B_135]: (~r2_hidden('#skF_4'(A_133, k4_xboole_0(A_134, B_135)), B_135) | ~r2_hidden(A_133, k4_xboole_0(A_134, B_135)))), inference(resolution, [status(thm)], [c_53, c_4])).
% 3.37/1.55  tff(c_1024, plain, (![A_30, A_1]: (~r2_hidden(A_30, k4_xboole_0(A_1, A_1)))), inference(resolution, [status(thm)], [c_67, c_1014])).
% 3.37/1.55  tff(c_1038, plain, (![A_136]: (~r2_hidden(A_136, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_1024])).
% 3.37/1.55  tff(c_1050, plain, (![B_2, C_3]: (r2_hidden('#skF_2'(k1_xboole_0, B_2, C_3), C_3) | k4_xboole_0(k1_xboole_0, B_2)=C_3)), inference(resolution, [status(thm)], [c_18, c_1038])).
% 3.37/1.55  tff(c_1082, plain, (![B_2, C_3]: (r2_hidden('#skF_2'(k1_xboole_0, B_2, C_3), C_3) | k1_xboole_0=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_864, c_1050])).
% 3.37/1.55  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.55  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.55  tff(c_157, plain, (![D_52, A_53, B_54]: (~r2_hidden(D_52, '#skF_4'(A_53, B_54)) | ~r2_hidden(D_52, B_54) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.55  tff(c_1857, plain, (![A_189, B_190, B_191]: (~r2_hidden('#skF_3'('#skF_4'(A_189, B_190), B_191), B_190) | ~r2_hidden(A_189, B_190) | r1_xboole_0('#skF_4'(A_189, B_190), B_191))), inference(resolution, [status(thm)], [c_24, c_157])).
% 3.37/1.55  tff(c_1875, plain, (![A_192, B_193]: (~r2_hidden(A_192, B_193) | r1_xboole_0('#skF_4'(A_192, B_193), B_193))), inference(resolution, [status(thm)], [c_22, c_1857])).
% 3.37/1.55  tff(c_32, plain, (![B_21]: (~r1_xboole_0(B_21, '#skF_5') | ~r2_hidden(B_21, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.37/1.55  tff(c_68, plain, (![A_30]: (~r1_xboole_0('#skF_4'(A_30, '#skF_5'), '#skF_5') | ~r2_hidden(A_30, '#skF_5'))), inference(resolution, [status(thm)], [c_53, c_32])).
% 3.37/1.55  tff(c_1906, plain, (![A_196]: (~r2_hidden(A_196, '#skF_5'))), inference(resolution, [status(thm)], [c_1875, c_68])).
% 3.37/1.55  tff(c_1928, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1082, c_1906])).
% 3.37/1.55  tff(c_1974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1928])).
% 3.37/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.55  
% 3.37/1.55  Inference rules
% 3.37/1.55  ----------------------
% 3.37/1.55  #Ref     : 0
% 3.37/1.55  #Sup     : 408
% 3.37/1.55  #Fact    : 0
% 3.37/1.55  #Define  : 0
% 3.37/1.55  #Split   : 0
% 3.37/1.55  #Chain   : 0
% 3.37/1.55  #Close   : 0
% 3.37/1.55  
% 3.37/1.55  Ordering : KBO
% 3.37/1.55  
% 3.37/1.55  Simplification rules
% 3.37/1.55  ----------------------
% 3.37/1.55  #Subsume      : 110
% 3.37/1.55  #Demod        : 195
% 3.37/1.55  #Tautology    : 129
% 3.37/1.55  #SimpNegUnit  : 11
% 3.37/1.55  #BackRed      : 7
% 3.37/1.55  
% 3.37/1.55  #Partial instantiations: 0
% 3.37/1.55  #Strategies tried      : 1
% 3.37/1.55  
% 3.37/1.55  Timing (in seconds)
% 3.37/1.55  ----------------------
% 3.37/1.55  Preprocessing        : 0.28
% 3.37/1.55  Parsing              : 0.14
% 3.37/1.55  CNF conversion       : 0.02
% 3.37/1.55  Main loop            : 0.51
% 3.37/1.55  Inferencing          : 0.20
% 3.37/1.55  Reduction            : 0.14
% 3.37/1.55  Demodulation         : 0.10
% 3.37/1.55  BG Simplification    : 0.02
% 3.37/1.55  Subsumption          : 0.11
% 3.37/1.55  Abstraction          : 0.02
% 3.47/1.55  MUC search           : 0.00
% 3.47/1.55  Cooper               : 0.00
% 3.47/1.55  Total                : 0.82
% 3.47/1.55  Index Insertion      : 0.00
% 3.47/1.55  Index Deletion       : 0.00
% 3.47/1.55  Index Matching       : 0.00
% 3.47/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
