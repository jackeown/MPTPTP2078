%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:21 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   63 (  75 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   94 ( 138 expanded)
%              Number of equality atoms :   55 (  67 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(c_68,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_26,plain,(
    ! [B_34] : k4_xboole_0(k1_tarski(B_34),k1_tarski(B_34)) != k1_tarski(B_34) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_108,plain,(
    ! [B_34] : k1_tarski(B_34) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_26])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_74,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_70,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_305,plain,(
    ! [D_153,C_154,B_155,A_156] :
      ( r2_hidden(k1_funct_1(D_153,C_154),B_155)
      | k1_xboole_0 = B_155
      | ~ r2_hidden(C_154,A_156)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155)))
      | ~ v1_funct_2(D_153,A_156,B_155)
      | ~ v1_funct_1(D_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_417,plain,(
    ! [D_171,B_172] :
      ( r2_hidden(k1_funct_1(D_171,'#skF_5'),B_172)
      | k1_xboole_0 = B_172
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_172)))
      | ~ v1_funct_2(D_171,'#skF_3',B_172)
      | ~ v1_funct_1(D_171) ) ),
    inference(resolution,[status(thm)],[c_70,c_305])).

tff(c_420,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_417])).

tff(c_423,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_420])).

tff(c_424,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_423])).

tff(c_12,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_276,plain,(
    ! [C_148,E_149,D_150,B_151,G_152,A_147] :
      ( G_152 = E_149
      | G_152 = D_150
      | G_152 = C_148
      | G_152 = B_151
      | G_152 = A_147
      | ~ r2_hidden(G_152,k3_enumset1(A_147,B_151,C_148,D_150,E_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_354,plain,(
    ! [G_159,D_161,A_158,B_160,C_157] :
      ( G_159 = D_161
      | G_159 = C_157
      | G_159 = B_160
      | G_159 = A_158
      | G_159 = A_158
      | ~ r2_hidden(G_159,k2_enumset1(A_158,B_160,C_157,D_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_276])).

tff(c_378,plain,(
    ! [G_162,C_163,B_164,A_165] :
      ( G_162 = C_163
      | G_162 = B_164
      | G_162 = A_165
      | G_162 = A_165
      | G_162 = A_165
      | ~ r2_hidden(G_162,k1_enumset1(A_165,B_164,C_163)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_354])).

tff(c_397,plain,(
    ! [G_166,B_167,A_168] :
      ( G_166 = B_167
      | G_166 = A_168
      | G_166 = A_168
      | G_166 = A_168
      | G_166 = A_168
      | ~ r2_hidden(G_166,k2_tarski(A_168,B_167)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_378])).

tff(c_406,plain,(
    ! [G_166,A_5] :
      ( G_166 = A_5
      | G_166 = A_5
      | G_166 = A_5
      | G_166 = A_5
      | G_166 = A_5
      | ~ r2_hidden(G_166,k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_397])).

tff(c_428,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_424,c_406])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_68,c_68,c_68,c_428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:37:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.40  
% 2.84/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.41  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.84/1.41  
% 2.84/1.41  %Foreground sorts:
% 2.84/1.41  
% 2.84/1.41  
% 2.84/1.41  %Background operators:
% 2.84/1.41  
% 2.84/1.41  
% 2.84/1.41  %Foreground operators:
% 2.84/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.84/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.84/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.84/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.41  
% 2.84/1.42  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.84/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.42  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.84/1.42  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.84/1.42  tff(f_87, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.84/1.42  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.42  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.84/1.42  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.84/1.42  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.84/1.42  tff(f_75, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.84/1.42  tff(c_68, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.84/1.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.42  tff(c_99, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.42  tff(c_107, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.84/1.42  tff(c_26, plain, (![B_34]: (k4_xboole_0(k1_tarski(B_34), k1_tarski(B_34))!=k1_tarski(B_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.42  tff(c_108, plain, (![B_34]: (k1_tarski(B_34)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_26])).
% 2.84/1.42  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.84/1.42  tff(c_74, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.84/1.42  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.84/1.42  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.84/1.42  tff(c_305, plain, (![D_153, C_154, B_155, A_156]: (r2_hidden(k1_funct_1(D_153, C_154), B_155) | k1_xboole_0=B_155 | ~r2_hidden(C_154, A_156) | ~m1_subset_1(D_153, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))) | ~v1_funct_2(D_153, A_156, B_155) | ~v1_funct_1(D_153))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.84/1.42  tff(c_417, plain, (![D_171, B_172]: (r2_hidden(k1_funct_1(D_171, '#skF_5'), B_172) | k1_xboole_0=B_172 | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_172))) | ~v1_funct_2(D_171, '#skF_3', B_172) | ~v1_funct_1(D_171))), inference(resolution, [status(thm)], [c_70, c_305])).
% 2.84/1.42  tff(c_420, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_417])).
% 2.84/1.42  tff(c_423, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_420])).
% 2.84/1.42  tff(c_424, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_108, c_423])).
% 2.84/1.42  tff(c_12, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.42  tff(c_14, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.42  tff(c_16, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.42  tff(c_18, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.42  tff(c_276, plain, (![C_148, E_149, D_150, B_151, G_152, A_147]: (G_152=E_149 | G_152=D_150 | G_152=C_148 | G_152=B_151 | G_152=A_147 | ~r2_hidden(G_152, k3_enumset1(A_147, B_151, C_148, D_150, E_149)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.84/1.42  tff(c_354, plain, (![G_159, D_161, A_158, B_160, C_157]: (G_159=D_161 | G_159=C_157 | G_159=B_160 | G_159=A_158 | G_159=A_158 | ~r2_hidden(G_159, k2_enumset1(A_158, B_160, C_157, D_161)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_276])).
% 2.84/1.42  tff(c_378, plain, (![G_162, C_163, B_164, A_165]: (G_162=C_163 | G_162=B_164 | G_162=A_165 | G_162=A_165 | G_162=A_165 | ~r2_hidden(G_162, k1_enumset1(A_165, B_164, C_163)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_354])).
% 2.84/1.42  tff(c_397, plain, (![G_166, B_167, A_168]: (G_166=B_167 | G_166=A_168 | G_166=A_168 | G_166=A_168 | G_166=A_168 | ~r2_hidden(G_166, k2_tarski(A_168, B_167)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_378])).
% 2.84/1.42  tff(c_406, plain, (![G_166, A_5]: (G_166=A_5 | G_166=A_5 | G_166=A_5 | G_166=A_5 | G_166=A_5 | ~r2_hidden(G_166, k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_397])).
% 2.84/1.42  tff(c_428, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_424, c_406])).
% 2.84/1.42  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_68, c_68, c_68, c_428])).
% 2.84/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.42  
% 2.84/1.42  Inference rules
% 2.84/1.42  ----------------------
% 2.84/1.42  #Ref     : 0
% 2.84/1.42  #Sup     : 80
% 2.84/1.42  #Fact    : 0
% 2.84/1.42  #Define  : 0
% 2.84/1.42  #Split   : 0
% 2.84/1.42  #Chain   : 0
% 2.84/1.42  #Close   : 0
% 2.84/1.42  
% 2.84/1.42  Ordering : KBO
% 2.84/1.42  
% 2.84/1.42  Simplification rules
% 2.84/1.42  ----------------------
% 2.84/1.42  #Subsume      : 1
% 2.84/1.42  #Demod        : 11
% 2.84/1.42  #Tautology    : 44
% 2.84/1.42  #SimpNegUnit  : 4
% 2.84/1.42  #BackRed      : 1
% 2.84/1.42  
% 2.84/1.42  #Partial instantiations: 0
% 2.84/1.42  #Strategies tried      : 1
% 2.84/1.42  
% 2.84/1.42  Timing (in seconds)
% 2.84/1.42  ----------------------
% 2.84/1.42  Preprocessing        : 0.36
% 2.84/1.42  Parsing              : 0.18
% 2.84/1.42  CNF conversion       : 0.03
% 2.84/1.42  Main loop            : 0.31
% 2.84/1.42  Inferencing          : 0.11
% 2.84/1.43  Reduction            : 0.09
% 2.84/1.43  Demodulation         : 0.07
% 2.84/1.43  BG Simplification    : 0.02
% 2.84/1.43  Subsumption          : 0.07
% 2.84/1.43  Abstraction          : 0.02
% 2.84/1.43  MUC search           : 0.00
% 2.84/1.43  Cooper               : 0.00
% 2.84/1.43  Total                : 0.70
% 2.84/1.43  Index Insertion      : 0.00
% 2.84/1.43  Index Deletion       : 0.00
% 2.84/1.43  Index Matching       : 0.00
% 2.84/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
