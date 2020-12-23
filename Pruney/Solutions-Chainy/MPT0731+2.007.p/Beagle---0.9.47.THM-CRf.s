%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:01 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   61 (  72 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   54 (  73 expanded)
%              Number of equality atoms :   26 (  44 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_72,axiom,(
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

tff(f_83,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_74,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(c_264,plain,(
    ! [B_188,A_190,E_189,F_187,D_191,C_192] : k5_enumset1(A_190,A_190,B_188,C_192,D_191,E_189,F_187) = k4_enumset1(A_190,B_188,C_192,D_191,E_189,F_187) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [D_36,F_38,I_43,E_37,A_33,B_34,C_35] : r2_hidden(I_43,k5_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,I_43)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_636,plain,(
    ! [C_342,E_345,D_341,F_346,A_344,B_343] : r2_hidden(F_346,k4_enumset1(A_344,B_343,C_342,D_341,E_345,F_346)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_22])).

tff(c_644,plain,(
    ! [B_349,D_350,A_348,E_351,C_347] : r2_hidden(E_351,k3_enumset1(A_348,B_349,C_347,D_350,E_351)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_636])).

tff(c_652,plain,(
    ! [D_352,A_353,B_354,C_355] : r2_hidden(D_352,k2_enumset1(A_353,B_354,C_355,D_352)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_644])).

tff(c_660,plain,(
    ! [C_356,A_357,B_358] : r2_hidden(C_356,k1_enumset1(A_357,B_358,C_356)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_652])).

tff(c_666,plain,(
    ! [B_3,A_2] : r2_hidden(B_3,k2_tarski(A_2,B_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_660])).

tff(c_72,plain,(
    k1_ordinal1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [A_44] : k2_xboole_0(A_44,k1_tarski(A_44)) = k1_ordinal1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,k3_tarski(B_30))
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [D_36,G_39,I_43,E_37,A_33,B_34,C_35] : r2_hidden(I_43,k5_enumset1(A_33,B_34,C_35,D_36,E_37,I_43,G_39)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_323,plain,(
    ! [E_197,D_193,C_194,F_198,A_196,B_195] : r2_hidden(E_197,k4_enumset1(A_196,B_195,C_194,D_193,E_197,F_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_24])).

tff(c_331,plain,(
    ! [A_200,C_199,E_203,D_202,B_201] : r2_hidden(D_202,k3_enumset1(A_200,B_201,C_199,D_202,E_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_323])).

tff(c_339,plain,(
    ! [C_204,A_205,B_206,D_207] : r2_hidden(C_204,k2_enumset1(A_205,B_206,C_204,D_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_331])).

tff(c_347,plain,(
    ! [B_208,A_209,C_210] : r2_hidden(B_208,k1_enumset1(A_209,B_208,C_210)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_339])).

tff(c_355,plain,(
    ! [A_211,B_212] : r2_hidden(A_211,k2_tarski(A_211,B_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_347])).

tff(c_376,plain,(
    ! [A_220] : r2_hidden(A_220,k1_tarski(A_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_355])).

tff(c_70,plain,(
    ! [B_46,A_45] :
      ( ~ r1_tarski(B_46,A_45)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_384,plain,(
    ! [A_221] : ~ r1_tarski(k1_tarski(A_221),A_221) ),
    inference(resolution,[status(thm)],[c_376,c_70])).

tff(c_456,plain,(
    ! [B_244] : ~ r2_hidden(k1_tarski(k3_tarski(B_244)),B_244) ),
    inference(resolution,[status(thm)],[c_16,c_384])).

tff(c_537,plain,(
    ! [A_285,B_286] : ~ r2_hidden(k1_tarski(k2_xboole_0(A_285,B_286)),k2_tarski(A_285,B_286)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_456])).

tff(c_548,plain,(
    ! [A_287] : ~ r2_hidden(k1_tarski(k1_ordinal1(A_287)),k2_tarski(A_287,k1_tarski(A_287))) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_537])).

tff(c_551,plain,(
    ~ r2_hidden(k1_tarski('#skF_3'),k2_tarski('#skF_3',k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_548])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:28:45 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.39  
% 2.92/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.40  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2
% 2.92/1.40  
% 2.92/1.40  %Foreground sorts:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Background operators:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Foreground operators:
% 2.92/1.40  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.92/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.40  
% 2.92/1.41  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.92/1.41  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.92/1.41  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.92/1.41  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.92/1.41  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.92/1.41  tff(f_72, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_enumset1)).
% 2.92/1.41  tff(f_83, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 2.92/1.41  tff(f_74, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.92/1.41  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.92/1.41  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.92/1.41  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.92/1.41  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.92/1.41  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.41  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.41  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.41  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.41  tff(c_264, plain, (![B_188, A_190, E_189, F_187, D_191, C_192]: (k5_enumset1(A_190, A_190, B_188, C_192, D_191, E_189, F_187)=k4_enumset1(A_190, B_188, C_192, D_191, E_189, F_187))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.41  tff(c_22, plain, (![D_36, F_38, I_43, E_37, A_33, B_34, C_35]: (r2_hidden(I_43, k5_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, I_43)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.92/1.41  tff(c_636, plain, (![C_342, E_345, D_341, F_346, A_344, B_343]: (r2_hidden(F_346, k4_enumset1(A_344, B_343, C_342, D_341, E_345, F_346)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_22])).
% 2.92/1.41  tff(c_644, plain, (![B_349, D_350, A_348, E_351, C_347]: (r2_hidden(E_351, k3_enumset1(A_348, B_349, C_347, D_350, E_351)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_636])).
% 2.92/1.41  tff(c_652, plain, (![D_352, A_353, B_354, C_355]: (r2_hidden(D_352, k2_enumset1(A_353, B_354, C_355, D_352)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_644])).
% 2.92/1.41  tff(c_660, plain, (![C_356, A_357, B_358]: (r2_hidden(C_356, k1_enumset1(A_357, B_358, C_356)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_652])).
% 2.92/1.41  tff(c_666, plain, (![B_3, A_2]: (r2_hidden(B_3, k2_tarski(A_2, B_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_660])).
% 2.92/1.41  tff(c_72, plain, (k1_ordinal1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.92/1.41  tff(c_68, plain, (![A_44]: (k2_xboole_0(A_44, k1_tarski(A_44))=k1_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.92/1.41  tff(c_18, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.41  tff(c_16, plain, (![A_29, B_30]: (r1_tarski(A_29, k3_tarski(B_30)) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.92/1.41  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.41  tff(c_24, plain, (![D_36, G_39, I_43, E_37, A_33, B_34, C_35]: (r2_hidden(I_43, k5_enumset1(A_33, B_34, C_35, D_36, E_37, I_43, G_39)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.92/1.41  tff(c_323, plain, (![E_197, D_193, C_194, F_198, A_196, B_195]: (r2_hidden(E_197, k4_enumset1(A_196, B_195, C_194, D_193, E_197, F_198)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_24])).
% 2.92/1.41  tff(c_331, plain, (![A_200, C_199, E_203, D_202, B_201]: (r2_hidden(D_202, k3_enumset1(A_200, B_201, C_199, D_202, E_203)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_323])).
% 2.92/1.41  tff(c_339, plain, (![C_204, A_205, B_206, D_207]: (r2_hidden(C_204, k2_enumset1(A_205, B_206, C_204, D_207)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_331])).
% 2.92/1.41  tff(c_347, plain, (![B_208, A_209, C_210]: (r2_hidden(B_208, k1_enumset1(A_209, B_208, C_210)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_339])).
% 2.92/1.41  tff(c_355, plain, (![A_211, B_212]: (r2_hidden(A_211, k2_tarski(A_211, B_212)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_347])).
% 2.92/1.41  tff(c_376, plain, (![A_220]: (r2_hidden(A_220, k1_tarski(A_220)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_355])).
% 2.92/1.41  tff(c_70, plain, (![B_46, A_45]: (~r1_tarski(B_46, A_45) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.92/1.41  tff(c_384, plain, (![A_221]: (~r1_tarski(k1_tarski(A_221), A_221))), inference(resolution, [status(thm)], [c_376, c_70])).
% 2.92/1.41  tff(c_456, plain, (![B_244]: (~r2_hidden(k1_tarski(k3_tarski(B_244)), B_244))), inference(resolution, [status(thm)], [c_16, c_384])).
% 2.92/1.41  tff(c_537, plain, (![A_285, B_286]: (~r2_hidden(k1_tarski(k2_xboole_0(A_285, B_286)), k2_tarski(A_285, B_286)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_456])).
% 2.92/1.41  tff(c_548, plain, (![A_287]: (~r2_hidden(k1_tarski(k1_ordinal1(A_287)), k2_tarski(A_287, k1_tarski(A_287))))), inference(superposition, [status(thm), theory('equality')], [c_68, c_537])).
% 2.92/1.41  tff(c_551, plain, (~r2_hidden(k1_tarski('#skF_3'), k2_tarski('#skF_3', k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_548])).
% 2.92/1.41  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_666, c_551])).
% 2.92/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.41  
% 2.92/1.41  Inference rules
% 2.92/1.41  ----------------------
% 2.92/1.41  #Ref     : 0
% 2.92/1.41  #Sup     : 142
% 2.92/1.41  #Fact    : 0
% 2.92/1.41  #Define  : 0
% 2.92/1.41  #Split   : 0
% 2.92/1.41  #Chain   : 0
% 2.92/1.41  #Close   : 0
% 2.92/1.41  
% 2.92/1.41  Ordering : KBO
% 2.92/1.41  
% 2.92/1.41  Simplification rules
% 2.92/1.41  ----------------------
% 2.92/1.41  #Subsume      : 18
% 2.92/1.41  #Demod        : 5
% 2.92/1.41  #Tautology    : 34
% 2.92/1.41  #SimpNegUnit  : 0
% 2.92/1.41  #BackRed      : 1
% 2.92/1.41  
% 2.92/1.41  #Partial instantiations: 0
% 2.92/1.41  #Strategies tried      : 1
% 2.92/1.41  
% 2.92/1.41  Timing (in seconds)
% 2.92/1.41  ----------------------
% 2.92/1.41  Preprocessing        : 0.32
% 2.92/1.41  Parsing              : 0.15
% 2.92/1.41  CNF conversion       : 0.02
% 2.92/1.41  Main loop            : 0.34
% 2.92/1.41  Inferencing          : 0.12
% 2.92/1.41  Reduction            : 0.09
% 2.92/1.41  Demodulation         : 0.07
% 2.92/1.41  BG Simplification    : 0.02
% 2.92/1.42  Subsumption          : 0.09
% 2.92/1.42  Abstraction          : 0.02
% 2.92/1.42  MUC search           : 0.00
% 2.92/1.42  Cooper               : 0.00
% 2.92/1.42  Total                : 0.69
% 2.92/1.42  Index Insertion      : 0.00
% 2.92/1.42  Index Deletion       : 0.00
% 2.92/1.42  Index Matching       : 0.00
% 2.92/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
