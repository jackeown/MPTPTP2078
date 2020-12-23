%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:29 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   71 (  83 expanded)
%              Number of leaves         :   40 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 141 expanded)
%              Number of equality atoms :   49 (  61 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_66,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_98,plain,(
    ! [A_58,B_59] : ~ r2_hidden(A_58,k2_zfmisc_1(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_98])).

tff(c_6,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_4'(A_37),A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_146,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [A_86,B_87] :
      ( ~ r1_xboole_0(A_86,B_87)
      | k3_xboole_0(A_86,B_87) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_146])).

tff(c_156,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_218,plain,(
    ! [A_105,C_106,B_107] :
      ( r2_hidden(A_105,C_106)
      | k3_xboole_0(k2_tarski(A_105,B_107),C_106) != k2_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_222,plain,(
    ! [A_105,B_107] :
      ( r2_hidden(A_105,k1_xboole_0)
      | k2_tarski(A_105,B_107) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_218])).

tff(c_228,plain,(
    ! [A_108,B_109] : k2_tarski(A_108,B_109) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_222])).

tff(c_230,plain,(
    ! [A_7] : k1_tarski(A_7) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_228])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_72,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_638,plain,(
    ! [D_239,C_240,B_241,A_242] :
      ( r2_hidden(k1_funct_1(D_239,C_240),B_241)
      | k1_xboole_0 = B_241
      | ~ r2_hidden(C_240,A_242)
      | ~ m1_subset_1(D_239,k1_zfmisc_1(k2_zfmisc_1(A_242,B_241)))
      | ~ v1_funct_2(D_239,A_242,B_241)
      | ~ v1_funct_1(D_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1703,plain,(
    ! [D_3567,B_3568] :
      ( r2_hidden(k1_funct_1(D_3567,'#skF_7'),B_3568)
      | k1_xboole_0 = B_3568
      | ~ m1_subset_1(D_3567,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_3568)))
      | ~ v1_funct_2(D_3567,'#skF_5',B_3568)
      | ~ v1_funct_1(D_3567) ) ),
    inference(resolution,[status(thm)],[c_68,c_638])).

tff(c_1708,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_1703])).

tff(c_1715,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1708])).

tff(c_1716,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_1715])).

tff(c_10,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_373,plain,(
    ! [C_162,B_159,D_158,A_160,F_161] :
      ( F_161 = D_158
      | F_161 = C_162
      | F_161 = B_159
      | F_161 = A_160
      | ~ r2_hidden(F_161,k2_enumset1(A_160,B_159,C_162,D_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_407,plain,(
    ! [F_170,C_171,B_172,A_173] :
      ( F_170 = C_171
      | F_170 = B_172
      | F_170 = A_173
      | F_170 = A_173
      | ~ r2_hidden(F_170,k1_enumset1(A_173,B_172,C_171)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_373])).

tff(c_431,plain,(
    ! [F_174,B_175,A_176] :
      ( F_174 = B_175
      | F_174 = A_176
      | F_174 = A_176
      | F_174 = A_176
      | ~ r2_hidden(F_174,k2_tarski(A_176,B_175)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_407])).

tff(c_444,plain,(
    ! [F_174,A_7] :
      ( F_174 = A_7
      | F_174 = A_7
      | F_174 = A_7
      | F_174 = A_7
      | ~ r2_hidden(F_174,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_431])).

tff(c_1723,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1716,c_444])).

tff(c_1732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_66,c_66,c_1723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.84  
% 4.16/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.84  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_1
% 4.16/1.84  
% 4.16/1.84  %Foreground sorts:
% 4.16/1.84  
% 4.16/1.84  
% 4.16/1.84  %Background operators:
% 4.16/1.84  
% 4.16/1.84  
% 4.16/1.84  %Foreground operators:
% 4.16/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.84  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.16/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.16/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 4.16/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.84  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.16/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.16/1.84  tff('#skF_7', type, '#skF_7': $i).
% 4.16/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.16/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.16/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.16/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.16/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.16/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.16/1.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.16/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.16/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 4.16/1.84  tff('#skF_8', type, '#skF_8': $i).
% 4.16/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.16/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.16/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.84  
% 4.16/1.86  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.16/1.86  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.16/1.86  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.16/1.86  tff(f_60, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.16/1.86  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.16/1.86  tff(f_98, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.16/1.86  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.16/1.86  tff(f_64, axiom, (![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 4.16/1.86  tff(f_110, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.16/1.86  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.16/1.86  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.16/1.86  tff(f_82, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 4.16/1.86  tff(c_66, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.16/1.86  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.16/1.86  tff(c_20, plain, (![A_22]: (k2_zfmisc_1(A_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.16/1.86  tff(c_98, plain, (![A_58, B_59]: (~r2_hidden(A_58, k2_zfmisc_1(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.16/1.86  tff(c_101, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_98])).
% 4.16/1.86  tff(c_6, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.16/1.86  tff(c_58, plain, (![A_37]: (r2_hidden('#skF_4'(A_37), A_37) | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.16/1.86  tff(c_146, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.16/1.86  tff(c_152, plain, (![A_86, B_87]: (~r1_xboole_0(A_86, B_87) | k3_xboole_0(A_86, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_146])).
% 4.16/1.86  tff(c_156, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_152])).
% 4.16/1.86  tff(c_218, plain, (![A_105, C_106, B_107]: (r2_hidden(A_105, C_106) | k3_xboole_0(k2_tarski(A_105, B_107), C_106)!=k2_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.16/1.86  tff(c_222, plain, (![A_105, B_107]: (r2_hidden(A_105, k1_xboole_0) | k2_tarski(A_105, B_107)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_156, c_218])).
% 4.16/1.86  tff(c_228, plain, (![A_108, B_109]: (k2_tarski(A_108, B_109)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_101, c_222])).
% 4.16/1.86  tff(c_230, plain, (![A_7]: (k1_tarski(A_7)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_228])).
% 4.16/1.86  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.16/1.86  tff(c_72, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.16/1.86  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.16/1.86  tff(c_68, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.16/1.86  tff(c_638, plain, (![D_239, C_240, B_241, A_242]: (r2_hidden(k1_funct_1(D_239, C_240), B_241) | k1_xboole_0=B_241 | ~r2_hidden(C_240, A_242) | ~m1_subset_1(D_239, k1_zfmisc_1(k2_zfmisc_1(A_242, B_241))) | ~v1_funct_2(D_239, A_242, B_241) | ~v1_funct_1(D_239))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.16/1.86  tff(c_1703, plain, (![D_3567, B_3568]: (r2_hidden(k1_funct_1(D_3567, '#skF_7'), B_3568) | k1_xboole_0=B_3568 | ~m1_subset_1(D_3567, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_3568))) | ~v1_funct_2(D_3567, '#skF_5', B_3568) | ~v1_funct_1(D_3567))), inference(resolution, [status(thm)], [c_68, c_638])).
% 4.16/1.86  tff(c_1708, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_1703])).
% 4.16/1.86  tff(c_1715, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1708])).
% 4.16/1.86  tff(c_1716, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_230, c_1715])).
% 4.16/1.86  tff(c_10, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.16/1.86  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.16/1.86  tff(c_373, plain, (![C_162, B_159, D_158, A_160, F_161]: (F_161=D_158 | F_161=C_162 | F_161=B_159 | F_161=A_160 | ~r2_hidden(F_161, k2_enumset1(A_160, B_159, C_162, D_158)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.16/1.86  tff(c_407, plain, (![F_170, C_171, B_172, A_173]: (F_170=C_171 | F_170=B_172 | F_170=A_173 | F_170=A_173 | ~r2_hidden(F_170, k1_enumset1(A_173, B_172, C_171)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_373])).
% 4.16/1.86  tff(c_431, plain, (![F_174, B_175, A_176]: (F_174=B_175 | F_174=A_176 | F_174=A_176 | F_174=A_176 | ~r2_hidden(F_174, k2_tarski(A_176, B_175)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_407])).
% 4.16/1.86  tff(c_444, plain, (![F_174, A_7]: (F_174=A_7 | F_174=A_7 | F_174=A_7 | F_174=A_7 | ~r2_hidden(F_174, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_431])).
% 4.16/1.86  tff(c_1723, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1716, c_444])).
% 4.16/1.86  tff(c_1732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_66, c_66, c_1723])).
% 4.16/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.86  
% 4.16/1.86  Inference rules
% 4.16/1.86  ----------------------
% 4.16/1.86  #Ref     : 4
% 4.16/1.86  #Sup     : 239
% 4.16/1.86  #Fact    : 14
% 4.16/1.86  #Define  : 0
% 4.16/1.86  #Split   : 2
% 4.16/1.86  #Chain   : 0
% 4.16/1.86  #Close   : 0
% 4.16/1.86  
% 4.16/1.86  Ordering : KBO
% 4.16/1.86  
% 4.16/1.86  Simplification rules
% 4.16/1.86  ----------------------
% 4.16/1.86  #Subsume      : 57
% 4.16/1.86  #Demod        : 41
% 4.16/1.86  #Tautology    : 62
% 4.16/1.86  #SimpNegUnit  : 33
% 4.16/1.86  #BackRed      : 2
% 4.16/1.86  
% 4.16/1.86  #Partial instantiations: 1500
% 4.16/1.86  #Strategies tried      : 1
% 4.16/1.86  
% 4.16/1.86  Timing (in seconds)
% 4.16/1.86  ----------------------
% 4.16/1.86  Preprocessing        : 0.47
% 4.16/1.86  Parsing              : 0.21
% 4.16/1.86  CNF conversion       : 0.03
% 4.16/1.86  Main loop            : 0.61
% 4.16/1.86  Inferencing          : 0.29
% 4.16/1.86  Reduction            : 0.15
% 4.16/1.86  Demodulation         : 0.10
% 4.16/1.86  BG Simplification    : 0.04
% 4.16/1.86  Subsumption          : 0.10
% 4.16/1.86  Abstraction          : 0.06
% 4.16/1.86  MUC search           : 0.00
% 4.16/1.86  Cooper               : 0.00
% 4.16/1.86  Total                : 1.11
% 4.16/1.86  Index Insertion      : 0.00
% 4.16/1.86  Index Deletion       : 0.00
% 4.16/1.86  Index Matching       : 0.00
% 4.16/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
