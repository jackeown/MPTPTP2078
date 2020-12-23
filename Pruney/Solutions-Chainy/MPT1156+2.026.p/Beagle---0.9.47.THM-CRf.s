%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:40 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 115 expanded)
%              Number of leaves         :   43 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 250 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_92,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_90,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_88,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_86,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_72,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_124,plain,(
    ! [A_64,B_65] :
      ( k6_domain_1(A_64,B_65) = k1_tarski(B_65)
      | ~ m1_subset_1(B_65,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_128,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_124])).

tff(c_129,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_70,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(u1_struct_0(A_41))
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_132,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_70])).

tff(c_135,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132])).

tff(c_139,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_135])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_139])).

tff(c_144,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_230,plain,(
    ! [A_169,B_170] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_169),B_170),k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_orders_2(A_169)
      | ~ v3_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_236,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_230])).

tff(c_239,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_86,c_84,c_236])).

tff(c_240,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_239])).

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

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_193,plain,(
    ! [B_161,F_158,G_159,A_155,D_160,E_157,C_156] : k6_enumset1(A_155,A_155,B_161,C_156,D_160,E_157,F_158,G_159) = k5_enumset1(A_155,B_161,C_156,D_160,E_157,F_158,G_159) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [H_36,E_33,J_40,A_29,F_34,D_32,C_31,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,J_40,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_226,plain,(
    ! [F_163,E_166,A_165,G_167,C_168,B_162,D_164] : r2_hidden(F_163,k5_enumset1(A_165,B_162,C_168,D_164,E_166,F_163,G_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_20])).

tff(c_245,plain,(
    ! [C_176,B_172,A_174,E_173,D_175,F_171] : r2_hidden(E_173,k4_enumset1(A_174,B_172,C_176,D_175,E_173,F_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_226])).

tff(c_249,plain,(
    ! [A_178,E_181,C_177,B_179,D_180] : r2_hidden(D_180,k3_enumset1(A_178,B_179,C_177,D_180,E_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_245])).

tff(c_254,plain,(
    ! [C_182,A_183,B_184,D_185] : r2_hidden(C_182,k2_enumset1(A_183,B_184,C_182,D_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_249])).

tff(c_258,plain,(
    ! [B_186,A_187,C_188] : r2_hidden(B_186,k1_enumset1(A_187,B_186,C_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_254])).

tff(c_262,plain,(
    ! [A_189,B_190] : r2_hidden(A_189,k2_tarski(A_189,B_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_258])).

tff(c_265,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_262])).

tff(c_82,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_146,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_82])).

tff(c_323,plain,(
    ! [B_219,A_220,C_221] :
      ( ~ r2_hidden(B_219,k2_orders_2(A_220,C_221))
      | ~ r2_hidden(B_219,C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ m1_subset_1(B_219,u1_struct_0(A_220))
      | ~ l1_orders_2(A_220)
      | ~ v5_orders_2(A_220)
      | ~ v4_orders_2(A_220)
      | ~ v3_orders_2(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_325,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_146,c_323])).

tff(c_328,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_240,c_265,c_325])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.42  
% 2.97/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.42  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.97/1.42  
% 2.97/1.42  %Foreground sorts:
% 2.97/1.42  
% 2.97/1.42  
% 2.97/1.42  %Background operators:
% 2.97/1.42  
% 2.97/1.42  
% 2.97/1.42  %Foreground operators:
% 2.97/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.97/1.42  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.97/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.97/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.42  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.97/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.42  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.97/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.42  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.97/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.97/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.42  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.42  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.97/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.97/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.42  
% 2.97/1.44  tff(f_142, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 2.97/1.44  tff(f_81, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.97/1.44  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.97/1.44  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.97/1.44  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 2.97/1.44  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.97/1.44  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.97/1.44  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.97/1.44  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.97/1.44  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.97/1.44  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.97/1.44  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.97/1.44  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 2.97/1.44  tff(f_124, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 2.97/1.44  tff(c_94, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.97/1.44  tff(c_92, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.97/1.44  tff(c_90, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.97/1.44  tff(c_88, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.97/1.44  tff(c_86, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.97/1.44  tff(c_84, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.97/1.44  tff(c_72, plain, (![A_42]: (l1_struct_0(A_42) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.44  tff(c_124, plain, (![A_64, B_65]: (k6_domain_1(A_64, B_65)=k1_tarski(B_65) | ~m1_subset_1(B_65, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.44  tff(c_128, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_84, c_124])).
% 2.97/1.44  tff(c_129, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_128])).
% 2.97/1.44  tff(c_70, plain, (![A_41]: (~v1_xboole_0(u1_struct_0(A_41)) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.44  tff(c_132, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_129, c_70])).
% 2.97/1.44  tff(c_135, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_94, c_132])).
% 2.97/1.44  tff(c_139, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_72, c_135])).
% 2.97/1.44  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_139])).
% 2.97/1.44  tff(c_144, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_128])).
% 2.97/1.44  tff(c_230, plain, (![A_169, B_170]: (m1_subset_1(k6_domain_1(u1_struct_0(A_169), B_170), k1_zfmisc_1(u1_struct_0(A_169))) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_orders_2(A_169) | ~v3_orders_2(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.97/1.44  tff(c_236, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_230])).
% 2.97/1.44  tff(c_239, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_86, c_84, c_236])).
% 2.97/1.44  tff(c_240, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_239])).
% 2.97/1.44  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.44  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.97/1.44  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.44  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.44  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.44  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.44  tff(c_193, plain, (![B_161, F_158, G_159, A_155, D_160, E_157, C_156]: (k6_enumset1(A_155, A_155, B_161, C_156, D_160, E_157, F_158, G_159)=k5_enumset1(A_155, B_161, C_156, D_160, E_157, F_158, G_159))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.44  tff(c_20, plain, (![H_36, E_33, J_40, A_29, F_34, D_32, C_31, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, J_40, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.97/1.44  tff(c_226, plain, (![F_163, E_166, A_165, G_167, C_168, B_162, D_164]: (r2_hidden(F_163, k5_enumset1(A_165, B_162, C_168, D_164, E_166, F_163, G_167)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_20])).
% 2.97/1.44  tff(c_245, plain, (![C_176, B_172, A_174, E_173, D_175, F_171]: (r2_hidden(E_173, k4_enumset1(A_174, B_172, C_176, D_175, E_173, F_171)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_226])).
% 2.97/1.44  tff(c_249, plain, (![A_178, E_181, C_177, B_179, D_180]: (r2_hidden(D_180, k3_enumset1(A_178, B_179, C_177, D_180, E_181)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_245])).
% 2.97/1.44  tff(c_254, plain, (![C_182, A_183, B_184, D_185]: (r2_hidden(C_182, k2_enumset1(A_183, B_184, C_182, D_185)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_249])).
% 2.97/1.44  tff(c_258, plain, (![B_186, A_187, C_188]: (r2_hidden(B_186, k1_enumset1(A_187, B_186, C_188)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_254])).
% 2.97/1.44  tff(c_262, plain, (![A_189, B_190]: (r2_hidden(A_189, k2_tarski(A_189, B_190)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_258])).
% 2.97/1.44  tff(c_265, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_262])).
% 2.97/1.44  tff(c_82, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.97/1.44  tff(c_146, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_82])).
% 2.97/1.44  tff(c_323, plain, (![B_219, A_220, C_221]: (~r2_hidden(B_219, k2_orders_2(A_220, C_221)) | ~r2_hidden(B_219, C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~m1_subset_1(B_219, u1_struct_0(A_220)) | ~l1_orders_2(A_220) | ~v5_orders_2(A_220) | ~v4_orders_2(A_220) | ~v3_orders_2(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.97/1.44  tff(c_325, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_146, c_323])).
% 2.97/1.44  tff(c_328, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_240, c_265, c_325])).
% 2.97/1.44  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_328])).
% 2.97/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.44  
% 2.97/1.44  Inference rules
% 2.97/1.44  ----------------------
% 2.97/1.44  #Ref     : 0
% 2.97/1.44  #Sup     : 50
% 2.97/1.44  #Fact    : 0
% 2.97/1.44  #Define  : 0
% 2.97/1.44  #Split   : 2
% 2.97/1.44  #Chain   : 0
% 2.97/1.44  #Close   : 0
% 2.97/1.44  
% 2.97/1.44  Ordering : KBO
% 2.97/1.44  
% 2.97/1.44  Simplification rules
% 2.97/1.44  ----------------------
% 2.97/1.44  #Subsume      : 0
% 2.97/1.44  #Demod        : 15
% 2.97/1.44  #Tautology    : 24
% 2.97/1.44  #SimpNegUnit  : 4
% 2.97/1.44  #BackRed      : 1
% 2.97/1.44  
% 2.97/1.44  #Partial instantiations: 0
% 2.97/1.44  #Strategies tried      : 1
% 2.97/1.44  
% 2.97/1.44  Timing (in seconds)
% 2.97/1.44  ----------------------
% 2.97/1.44  Preprocessing        : 0.38
% 2.97/1.44  Parsing              : 0.18
% 2.97/1.44  CNF conversion       : 0.03
% 2.97/1.44  Main loop            : 0.29
% 2.97/1.44  Inferencing          : 0.09
% 2.97/1.44  Reduction            : 0.08
% 2.97/1.44  Demodulation         : 0.05
% 2.97/1.44  BG Simplification    : 0.02
% 2.97/1.44  Subsumption          : 0.08
% 2.97/1.44  Abstraction          : 0.02
% 2.97/1.44  MUC search           : 0.00
% 2.97/1.44  Cooper               : 0.00
% 2.97/1.44  Total                : 0.71
% 2.97/1.44  Index Insertion      : 0.00
% 2.97/1.44  Index Deletion       : 0.00
% 2.97/1.44  Index Matching       : 0.00
% 2.97/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
