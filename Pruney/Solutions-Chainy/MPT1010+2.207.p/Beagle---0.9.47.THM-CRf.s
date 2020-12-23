%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:33 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   61 (  77 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 154 expanded)
%              Number of equality atoms :   67 (  83 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(c_60,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_39,B_40] : k2_xboole_0(k1_tarski(A_39),k1_tarski(B_40)) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),B_19) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_100,plain,(
    ! [A_47,B_48] : k2_tarski(A_47,B_48) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_14])).

tff(c_102,plain,(
    ! [A_3] : k1_tarski(A_3) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_218,plain,(
    ! [D_126,C_127,B_128,A_129] :
      ( r2_hidden(k1_funct_1(D_126,C_127),B_128)
      | k1_xboole_0 = B_128
      | ~ r2_hidden(C_127,A_129)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128)))
      | ~ v1_funct_2(D_126,A_129,B_128)
      | ~ v1_funct_1(D_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_318,plain,(
    ! [D_165,B_166] :
      ( r2_hidden(k1_funct_1(D_165,'#skF_5'),B_166)
      | k1_xboole_0 = B_166
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_166)))
      | ~ v1_funct_2(D_165,'#skF_3',B_166)
      | ~ v1_funct_1(D_165) ) ),
    inference(resolution,[status(thm)],[c_62,c_218])).

tff(c_321,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_318])).

tff(c_324,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_321])).

tff(c_325,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_324])).

tff(c_6,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11,D_12] : k3_enumset1(A_9,A_9,B_10,C_11,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k4_enumset1(A_13,A_13,B_14,C_15,D_16,E_17) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [H_109,A_112,F_113,E_111,B_108,D_110,C_107] :
      ( H_109 = F_113
      | H_109 = E_111
      | H_109 = D_110
      | H_109 = C_107
      | H_109 = B_108
      | H_109 = A_112
      | ~ r2_hidden(H_109,k4_enumset1(A_112,B_108,C_107,D_110,E_111,F_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_329,plain,(
    ! [A_171,E_169,D_167,H_170,B_168,C_172] :
      ( H_170 = E_169
      | H_170 = D_167
      | H_170 = C_172
      | H_170 = B_168
      | H_170 = A_171
      | H_170 = A_171
      | ~ r2_hidden(H_170,k3_enumset1(A_171,B_168,C_172,D_167,E_169)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_171])).

tff(c_358,plain,(
    ! [B_174,D_176,A_177,H_173,C_175] :
      ( H_173 = D_176
      | H_173 = C_175
      | H_173 = B_174
      | H_173 = A_177
      | H_173 = A_177
      | H_173 = A_177
      | ~ r2_hidden(H_173,k2_enumset1(A_177,B_174,C_175,D_176)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_329])).

tff(c_382,plain,(
    ! [H_178,C_179,B_180,A_181] :
      ( H_178 = C_179
      | H_178 = B_180
      | H_178 = A_181
      | H_178 = A_181
      | H_178 = A_181
      | H_178 = A_181
      | ~ r2_hidden(H_178,k1_enumset1(A_181,B_180,C_179)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_358])).

tff(c_401,plain,(
    ! [H_182,B_183,A_184] :
      ( H_182 = B_183
      | H_182 = A_184
      | H_182 = A_184
      | H_182 = A_184
      | H_182 = A_184
      | H_182 = A_184
      | ~ r2_hidden(H_182,k2_tarski(A_184,B_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_382])).

tff(c_416,plain,(
    ! [H_192,A_193] :
      ( H_192 = A_193
      | H_192 = A_193
      | H_192 = A_193
      | H_192 = A_193
      | H_192 = A_193
      | H_192 = A_193
      | ~ r2_hidden(H_192,k1_tarski(A_193)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_401])).

tff(c_419,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_325,c_416])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_60,c_60,c_60,c_60,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:00:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  
% 2.70/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.70/1.42  
% 2.70/1.42  %Foreground sorts:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Background operators:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Foreground operators:
% 2.70/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.42  
% 2.70/1.44  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.70/1.44  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.44  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.70/1.44  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.70/1.44  tff(f_76, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.70/1.44  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.70/1.44  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.70/1.44  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.70/1.44  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.70/1.44  tff(f_64, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 2.70/1.44  tff(c_60, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.44  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.44  tff(c_88, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), k1_tarski(B_40))=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.44  tff(c_14, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.70/1.44  tff(c_100, plain, (![A_47, B_48]: (k2_tarski(A_47, B_48)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_88, c_14])).
% 2.70/1.44  tff(c_102, plain, (![A_3]: (k1_tarski(A_3)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_100])).
% 2.70/1.44  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.44  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.44  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.44  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.44  tff(c_218, plain, (![D_126, C_127, B_128, A_129]: (r2_hidden(k1_funct_1(D_126, C_127), B_128) | k1_xboole_0=B_128 | ~r2_hidden(C_127, A_129) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))) | ~v1_funct_2(D_126, A_129, B_128) | ~v1_funct_1(D_126))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.70/1.44  tff(c_318, plain, (![D_165, B_166]: (r2_hidden(k1_funct_1(D_165, '#skF_5'), B_166) | k1_xboole_0=B_166 | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_166))) | ~v1_funct_2(D_165, '#skF_3', B_166) | ~v1_funct_1(D_165))), inference(resolution, [status(thm)], [c_62, c_218])).
% 2.70/1.44  tff(c_321, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_318])).
% 2.70/1.44  tff(c_324, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_321])).
% 2.70/1.44  tff(c_325, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_102, c_324])).
% 2.70/1.44  tff(c_6, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.44  tff(c_8, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.44  tff(c_10, plain, (![A_9, B_10, C_11, D_12]: (k3_enumset1(A_9, A_9, B_10, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.44  tff(c_12, plain, (![E_17, A_13, B_14, C_15, D_16]: (k4_enumset1(A_13, A_13, B_14, C_15, D_16, E_17)=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.44  tff(c_171, plain, (![H_109, A_112, F_113, E_111, B_108, D_110, C_107]: (H_109=F_113 | H_109=E_111 | H_109=D_110 | H_109=C_107 | H_109=B_108 | H_109=A_112 | ~r2_hidden(H_109, k4_enumset1(A_112, B_108, C_107, D_110, E_111, F_113)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.44  tff(c_329, plain, (![A_171, E_169, D_167, H_170, B_168, C_172]: (H_170=E_169 | H_170=D_167 | H_170=C_172 | H_170=B_168 | H_170=A_171 | H_170=A_171 | ~r2_hidden(H_170, k3_enumset1(A_171, B_168, C_172, D_167, E_169)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_171])).
% 2.70/1.44  tff(c_358, plain, (![B_174, D_176, A_177, H_173, C_175]: (H_173=D_176 | H_173=C_175 | H_173=B_174 | H_173=A_177 | H_173=A_177 | H_173=A_177 | ~r2_hidden(H_173, k2_enumset1(A_177, B_174, C_175, D_176)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_329])).
% 2.70/1.44  tff(c_382, plain, (![H_178, C_179, B_180, A_181]: (H_178=C_179 | H_178=B_180 | H_178=A_181 | H_178=A_181 | H_178=A_181 | H_178=A_181 | ~r2_hidden(H_178, k1_enumset1(A_181, B_180, C_179)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_358])).
% 2.70/1.44  tff(c_401, plain, (![H_182, B_183, A_184]: (H_182=B_183 | H_182=A_184 | H_182=A_184 | H_182=A_184 | H_182=A_184 | H_182=A_184 | ~r2_hidden(H_182, k2_tarski(A_184, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_382])).
% 2.70/1.44  tff(c_416, plain, (![H_192, A_193]: (H_192=A_193 | H_192=A_193 | H_192=A_193 | H_192=A_193 | H_192=A_193 | H_192=A_193 | ~r2_hidden(H_192, k1_tarski(A_193)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_401])).
% 2.70/1.44  tff(c_419, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_325, c_416])).
% 2.70/1.44  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_60, c_60, c_60, c_60, c_419])).
% 2.70/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.44  
% 2.70/1.44  Inference rules
% 2.70/1.44  ----------------------
% 2.70/1.44  #Ref     : 0
% 2.70/1.44  #Sup     : 85
% 2.70/1.44  #Fact    : 0
% 2.70/1.44  #Define  : 0
% 2.70/1.44  #Split   : 0
% 2.70/1.44  #Chain   : 0
% 2.70/1.44  #Close   : 0
% 2.70/1.44  
% 2.70/1.44  Ordering : KBO
% 2.70/1.44  
% 2.70/1.44  Simplification rules
% 2.70/1.44  ----------------------
% 2.70/1.44  #Subsume      : 0
% 2.70/1.44  #Demod        : 7
% 2.70/1.44  #Tautology    : 37
% 2.70/1.44  #SimpNegUnit  : 2
% 2.70/1.44  #BackRed      : 0
% 2.70/1.44  
% 2.70/1.44  #Partial instantiations: 0
% 2.70/1.44  #Strategies tried      : 1
% 2.70/1.44  
% 2.70/1.44  Timing (in seconds)
% 2.70/1.44  ----------------------
% 2.70/1.44  Preprocessing        : 0.35
% 2.70/1.44  Parsing              : 0.18
% 2.70/1.44  CNF conversion       : 0.03
% 2.70/1.44  Main loop            : 0.29
% 2.70/1.44  Inferencing          : 0.10
% 2.70/1.44  Reduction            : 0.08
% 2.70/1.44  Demodulation         : 0.06
% 2.70/1.44  BG Simplification    : 0.02
% 2.70/1.44  Subsumption          : 0.07
% 2.70/1.44  Abstraction          : 0.02
% 2.70/1.44  MUC search           : 0.00
% 2.70/1.44  Cooper               : 0.00
% 2.70/1.44  Total                : 0.67
% 2.70/1.44  Index Insertion      : 0.00
% 2.70/1.44  Index Deletion       : 0.00
% 2.70/1.44  Index Matching       : 0.00
% 2.70/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
