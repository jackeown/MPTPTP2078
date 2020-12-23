%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:39 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   74 (  91 expanded)
%              Number of leaves         :   38 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 135 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_78,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_82,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_126,plain,(
    ! [A_81,B_82] :
      ( k6_domain_1(A_81,B_82) = k1_tarski(B_82)
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_129,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_126])).

tff(c_132,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_129])).

tff(c_80,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_133,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_80])).

tff(c_179,plain,(
    ! [A_171,B_172] :
      ( m1_subset_1(k6_domain_1(A_171,B_172),k1_zfmisc_1(A_171))
      | ~ m1_subset_1(B_172,A_171)
      | v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_188,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_179])).

tff(c_192,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_188])).

tff(c_193,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_192])).

tff(c_426,plain,(
    ! [B_216,A_217] :
      ( ~ v1_subset_1(B_216,A_217)
      | v1_xboole_0(B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(A_217))
      | ~ v1_zfmisc_1(A_217)
      | v1_xboole_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_429,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_193,c_426])).

tff(c_435,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_133,c_429])).

tff(c_436,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_435])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_441,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_436,c_2])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] : k3_enumset1(A_9,A_9,B_10,C_11,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k4_enumset1(A_13,A_13,B_14,C_15,D_16,E_17) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_559,plain,(
    ! [D_228,C_225,A_224,F_227,B_229,E_226] : k5_enumset1(A_224,A_224,B_229,C_225,D_228,E_226,F_227) = k4_enumset1(A_224,B_229,C_225,D_228,E_226,F_227) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [C_33,B_32,F_36,E_35,G_37,D_34,I_41] : r2_hidden(I_41,k5_enumset1(I_41,B_32,C_33,D_34,E_35,F_36,G_37)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_619,plain,(
    ! [C_237,F_239,B_242,E_240,D_241,A_238] : r2_hidden(A_238,k4_enumset1(A_238,B_242,C_237,D_241,E_240,F_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_34])).

tff(c_627,plain,(
    ! [A_246,E_245,D_243,B_244,C_247] : r2_hidden(A_246,k3_enumset1(A_246,B_244,C_247,D_243,E_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_619])).

tff(c_635,plain,(
    ! [A_248,B_249,C_250,D_251] : r2_hidden(A_248,k2_enumset1(A_248,B_249,C_250,D_251)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_627])).

tff(c_682,plain,(
    ! [A_260,B_261,C_262] : r2_hidden(A_260,k1_enumset1(A_260,B_261,C_262)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_635])).

tff(c_690,plain,(
    ! [A_263,B_264] : r2_hidden(A_263,k2_tarski(A_263,B_264)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_682])).

tff(c_698,plain,(
    ! [A_265] : r2_hidden(A_265,k1_tarski(A_265)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_690])).

tff(c_704,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_698])).

tff(c_70,plain,(
    ! [B_46,A_45] :
      ( ~ r1_tarski(B_46,A_45)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_708,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_704,c_70])).

tff(c_712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.22/1.50  
% 3.22/1.50  %Foreground sorts:
% 3.22/1.50  
% 3.22/1.50  
% 3.22/1.50  %Background operators:
% 3.22/1.50  
% 3.22/1.50  
% 3.22/1.50  %Foreground operators:
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.50  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.22/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.22/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.50  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.22/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.50  
% 3.43/1.51  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.43/1.51  tff(f_125, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.43/1.51  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.43/1.51  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.43/1.51  tff(f_113, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.43/1.51  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.43/1.51  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.43/1.51  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.43/1.51  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.43/1.51  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.43/1.51  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.43/1.51  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.43/1.51  tff(f_72, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 3.43/1.51  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.43/1.51  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.51  tff(c_84, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.43/1.51  tff(c_78, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.43/1.51  tff(c_82, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.43/1.51  tff(c_126, plain, (![A_81, B_82]: (k6_domain_1(A_81, B_82)=k1_tarski(B_82) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.43/1.51  tff(c_129, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_126])).
% 3.43/1.51  tff(c_132, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_84, c_129])).
% 3.43/1.51  tff(c_80, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.43/1.51  tff(c_133, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_80])).
% 3.43/1.51  tff(c_179, plain, (![A_171, B_172]: (m1_subset_1(k6_domain_1(A_171, B_172), k1_zfmisc_1(A_171)) | ~m1_subset_1(B_172, A_171) | v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.43/1.51  tff(c_188, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_132, c_179])).
% 3.43/1.51  tff(c_192, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_188])).
% 3.43/1.51  tff(c_193, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_84, c_192])).
% 3.43/1.51  tff(c_426, plain, (![B_216, A_217]: (~v1_subset_1(B_216, A_217) | v1_xboole_0(B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(A_217)) | ~v1_zfmisc_1(A_217) | v1_xboole_0(A_217))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.43/1.51  tff(c_429, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_193, c_426])).
% 3.43/1.51  tff(c_435, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_133, c_429])).
% 3.43/1.51  tff(c_436, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_84, c_435])).
% 3.43/1.51  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.51  tff(c_441, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_436, c_2])).
% 3.43/1.51  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.43/1.51  tff(c_8, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.43/1.51  tff(c_10, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.43/1.51  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (k3_enumset1(A_9, A_9, B_10, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.43/1.51  tff(c_14, plain, (![E_17, A_13, B_14, C_15, D_16]: (k4_enumset1(A_13, A_13, B_14, C_15, D_16, E_17)=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.43/1.51  tff(c_559, plain, (![D_228, C_225, A_224, F_227, B_229, E_226]: (k5_enumset1(A_224, A_224, B_229, C_225, D_228, E_226, F_227)=k4_enumset1(A_224, B_229, C_225, D_228, E_226, F_227))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.51  tff(c_34, plain, (![C_33, B_32, F_36, E_35, G_37, D_34, I_41]: (r2_hidden(I_41, k5_enumset1(I_41, B_32, C_33, D_34, E_35, F_36, G_37)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.43/1.51  tff(c_619, plain, (![C_237, F_239, B_242, E_240, D_241, A_238]: (r2_hidden(A_238, k4_enumset1(A_238, B_242, C_237, D_241, E_240, F_239)))), inference(superposition, [status(thm), theory('equality')], [c_559, c_34])).
% 3.43/1.51  tff(c_627, plain, (![A_246, E_245, D_243, B_244, C_247]: (r2_hidden(A_246, k3_enumset1(A_246, B_244, C_247, D_243, E_245)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_619])).
% 3.43/1.51  tff(c_635, plain, (![A_248, B_249, C_250, D_251]: (r2_hidden(A_248, k2_enumset1(A_248, B_249, C_250, D_251)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_627])).
% 3.43/1.51  tff(c_682, plain, (![A_260, B_261, C_262]: (r2_hidden(A_260, k1_enumset1(A_260, B_261, C_262)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_635])).
% 3.43/1.51  tff(c_690, plain, (![A_263, B_264]: (r2_hidden(A_263, k2_tarski(A_263, B_264)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_682])).
% 3.43/1.51  tff(c_698, plain, (![A_265]: (r2_hidden(A_265, k1_tarski(A_265)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_690])).
% 3.43/1.51  tff(c_704, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_441, c_698])).
% 3.43/1.51  tff(c_70, plain, (![B_46, A_45]: (~r1_tarski(B_46, A_45) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.43/1.51  tff(c_708, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_704, c_70])).
% 3.43/1.51  tff(c_712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_708])).
% 3.43/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.51  
% 3.43/1.51  Inference rules
% 3.43/1.51  ----------------------
% 3.43/1.51  #Ref     : 0
% 3.43/1.51  #Sup     : 145
% 3.43/1.51  #Fact    : 0
% 3.43/1.51  #Define  : 0
% 3.43/1.51  #Split   : 3
% 3.43/1.51  #Chain   : 0
% 3.43/1.51  #Close   : 0
% 3.43/1.51  
% 3.43/1.51  Ordering : KBO
% 3.43/1.51  
% 3.43/1.51  Simplification rules
% 3.43/1.51  ----------------------
% 3.43/1.51  #Subsume      : 6
% 3.43/1.51  #Demod        : 49
% 3.43/1.51  #Tautology    : 61
% 3.43/1.51  #SimpNegUnit  : 13
% 3.43/1.51  #BackRed      : 13
% 3.43/1.51  
% 3.43/1.51  #Partial instantiations: 0
% 3.43/1.51  #Strategies tried      : 1
% 3.43/1.51  
% 3.43/1.51  Timing (in seconds)
% 3.43/1.51  ----------------------
% 3.43/1.52  Preprocessing        : 0.37
% 3.43/1.52  Parsing              : 0.18
% 3.43/1.52  CNF conversion       : 0.03
% 3.43/1.52  Main loop            : 0.38
% 3.43/1.52  Inferencing          : 0.12
% 3.43/1.52  Reduction            : 0.11
% 3.43/1.52  Demodulation         : 0.07
% 3.43/1.52  BG Simplification    : 0.03
% 3.43/1.52  Subsumption          : 0.10
% 3.43/1.52  Abstraction          : 0.03
% 3.43/1.52  MUC search           : 0.00
% 3.43/1.52  Cooper               : 0.00
% 3.43/1.52  Total                : 0.79
% 3.43/1.52  Index Insertion      : 0.00
% 3.43/1.52  Index Deletion       : 0.00
% 3.43/1.52  Index Matching       : 0.00
% 3.43/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
