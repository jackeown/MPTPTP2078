%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:25 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   56 (  60 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 (  82 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_72,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [F_108,A_111,D_112,E_110,B_109,C_113] : k5_enumset1(A_111,A_111,B_109,C_113,D_112,E_110,F_108) = k4_enumset1(A_111,B_109,C_113,D_112,E_110,F_108) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [G_35,E_33,A_29,I_39,F_34,D_32,B_30] : r2_hidden(I_39,k5_enumset1(A_29,B_30,I_39,D_32,E_33,F_34,G_35)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,(
    ! [E_119,C_114,A_116,D_115,F_118,B_117] : r2_hidden(B_117,k4_enumset1(A_116,B_117,C_114,D_115,E_119,F_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_26])).

tff(c_170,plain,(
    ! [D_130,B_129,A_128,E_131,C_127] : r2_hidden(A_128,k3_enumset1(A_128,B_129,C_127,D_130,E_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_174,plain,(
    ! [A_132,B_133,C_134,D_135] : r2_hidden(A_132,k2_enumset1(A_132,B_133,C_134,D_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_170])).

tff(c_178,plain,(
    ! [A_136,B_137,C_138] : r2_hidden(A_136,k1_enumset1(A_136,B_137,C_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_174])).

tff(c_182,plain,(
    ! [A_139,B_140] : r2_hidden(A_139,k2_tarski(A_139,B_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_178])).

tff(c_185,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_182])).

tff(c_187,plain,(
    ! [D_142,C_143,B_144,A_145] :
      ( r2_hidden(k1_funct_1(D_142,C_143),B_144)
      | k1_xboole_0 = B_144
      | ~ r2_hidden(C_143,A_145)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144)))
      | ~ v1_funct_2(D_142,A_145,B_144)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_380,plain,(
    ! [D_248,A_249,B_250] :
      ( r2_hidden(k1_funct_1(D_248,A_249),B_250)
      | k1_xboole_0 = B_250
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_249),B_250)))
      | ~ v1_funct_2(D_248,k1_tarski(A_249),B_250)
      | ~ v1_funct_1(D_248) ) ),
    inference(resolution,[status(thm)],[c_185,c_187])).

tff(c_383,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_380])).

tff(c_386,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_383])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_66,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:39:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.41  
% 2.96/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.41  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.96/1.41  
% 2.96/1.41  %Foreground sorts:
% 2.96/1.41  
% 2.96/1.41  
% 2.96/1.41  %Background operators:
% 2.96/1.41  
% 2.96/1.41  
% 2.96/1.41  %Foreground operators:
% 2.96/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.96/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.96/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.96/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.41  
% 2.96/1.42  tff(f_90, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.96/1.42  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.96/1.42  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.96/1.42  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.96/1.42  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.96/1.42  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.96/1.42  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.96/1.42  tff(f_66, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_enumset1)).
% 2.96/1.42  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.96/1.42  tff(c_68, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.96/1.42  tff(c_66, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.96/1.42  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.96/1.42  tff(c_72, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.96/1.42  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.96/1.42  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.42  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.42  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.42  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.42  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.42  tff(c_127, plain, (![F_108, A_111, D_112, E_110, B_109, C_113]: (k5_enumset1(A_111, A_111, B_109, C_113, D_112, E_110, F_108)=k4_enumset1(A_111, B_109, C_113, D_112, E_110, F_108))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.42  tff(c_26, plain, (![G_35, E_33, A_29, I_39, F_34, D_32, B_30]: (r2_hidden(I_39, k5_enumset1(A_29, B_30, I_39, D_32, E_33, F_34, G_35)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.96/1.42  tff(c_157, plain, (![E_119, C_114, A_116, D_115, F_118, B_117]: (r2_hidden(B_117, k4_enumset1(A_116, B_117, C_114, D_115, E_119, F_118)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_26])).
% 2.96/1.42  tff(c_170, plain, (![D_130, B_129, A_128, E_131, C_127]: (r2_hidden(A_128, k3_enumset1(A_128, B_129, C_127, D_130, E_131)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_157])).
% 2.96/1.42  tff(c_174, plain, (![A_132, B_133, C_134, D_135]: (r2_hidden(A_132, k2_enumset1(A_132, B_133, C_134, D_135)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_170])).
% 2.96/1.42  tff(c_178, plain, (![A_136, B_137, C_138]: (r2_hidden(A_136, k1_enumset1(A_136, B_137, C_138)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_174])).
% 2.96/1.42  tff(c_182, plain, (![A_139, B_140]: (r2_hidden(A_139, k2_tarski(A_139, B_140)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_178])).
% 2.96/1.42  tff(c_185, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_182])).
% 2.96/1.42  tff(c_187, plain, (![D_142, C_143, B_144, A_145]: (r2_hidden(k1_funct_1(D_142, C_143), B_144) | k1_xboole_0=B_144 | ~r2_hidden(C_143, A_145) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))) | ~v1_funct_2(D_142, A_145, B_144) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.96/1.42  tff(c_380, plain, (![D_248, A_249, B_250]: (r2_hidden(k1_funct_1(D_248, A_249), B_250) | k1_xboole_0=B_250 | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_249), B_250))) | ~v1_funct_2(D_248, k1_tarski(A_249), B_250) | ~v1_funct_1(D_248))), inference(resolution, [status(thm)], [c_185, c_187])).
% 2.96/1.42  tff(c_383, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_380])).
% 2.96/1.42  tff(c_386, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_383])).
% 2.96/1.42  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_66, c_386])).
% 2.96/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.42  
% 2.96/1.42  Inference rules
% 2.96/1.42  ----------------------
% 2.96/1.42  #Ref     : 0
% 2.96/1.42  #Sup     : 78
% 2.96/1.42  #Fact    : 0
% 2.96/1.42  #Define  : 0
% 2.96/1.42  #Split   : 0
% 2.96/1.42  #Chain   : 0
% 2.96/1.42  #Close   : 0
% 2.96/1.42  
% 2.96/1.42  Ordering : KBO
% 2.96/1.42  
% 2.96/1.42  Simplification rules
% 2.96/1.42  ----------------------
% 2.96/1.42  #Subsume      : 0
% 2.96/1.42  #Demod        : 8
% 2.96/1.42  #Tautology    : 27
% 2.96/1.42  #SimpNegUnit  : 1
% 2.96/1.42  #BackRed      : 0
% 2.96/1.42  
% 2.96/1.42  #Partial instantiations: 0
% 2.96/1.42  #Strategies tried      : 1
% 2.96/1.42  
% 2.96/1.42  Timing (in seconds)
% 2.96/1.42  ----------------------
% 3.24/1.42  Preprocessing        : 0.37
% 3.24/1.42  Parsing              : 0.18
% 3.24/1.42  CNF conversion       : 0.03
% 3.24/1.42  Main loop            : 0.29
% 3.24/1.42  Inferencing          : 0.09
% 3.24/1.43  Reduction            : 0.08
% 3.24/1.43  Demodulation         : 0.06
% 3.24/1.43  BG Simplification    : 0.02
% 3.24/1.43  Subsumption          : 0.08
% 3.24/1.43  Abstraction          : 0.02
% 3.24/1.43  MUC search           : 0.00
% 3.24/1.43  Cooper               : 0.00
% 3.24/1.43  Total                : 0.68
% 3.24/1.43  Index Insertion      : 0.00
% 3.24/1.43  Index Deletion       : 0.00
% 3.24/1.43  Index Matching       : 0.00
% 3.24/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
