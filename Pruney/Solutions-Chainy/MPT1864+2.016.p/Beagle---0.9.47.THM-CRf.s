%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:16 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   53 (  88 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 270 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_83,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(A_60,C_61)
      | ~ r1_tarski(B_62,C_61)
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_83])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_214,plain,(
    ! [A_93,B_94,C_95] :
      ( v3_pre_topc('#skF_1'(A_93,B_94,C_95),A_93)
      | ~ r1_tarski(C_95,B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_351,plain,(
    ! [A_127,B_128,A_129] :
      ( v3_pre_topc('#skF_1'(A_127,B_128,A_129),A_127)
      | ~ r1_tarski(A_129,B_128)
      | ~ v2_tex_2(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ r1_tarski(A_129,u1_struct_0(A_127)) ) ),
    inference(resolution,[status(thm)],[c_14,c_214])).

tff(c_360,plain,(
    ! [A_127,A_9,A_129] :
      ( v3_pre_topc('#skF_1'(A_127,A_9,A_129),A_127)
      | ~ r1_tarski(A_129,A_9)
      | ~ v2_tex_2(A_9,A_127)
      | ~ l1_pre_topc(A_127)
      | ~ r1_tarski(A_129,u1_struct_0(A_127))
      | ~ r1_tarski(A_9,u1_struct_0(A_127)) ) ),
    inference(resolution,[status(thm)],[c_14,c_351])).

tff(c_497,plain,(
    ! [A_164,B_165,C_166] :
      ( k9_subset_1(u1_struct_0(A_164),B_165,'#skF_1'(A_164,B_165,C_166)) = C_166
      | ~ r1_tarski(C_166,B_165)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ v2_tex_2(B_165,A_164)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_623,plain,(
    ! [A_186,B_187,A_188] :
      ( k9_subset_1(u1_struct_0(A_186),B_187,'#skF_1'(A_186,B_187,A_188)) = A_188
      | ~ r1_tarski(A_188,B_187)
      | ~ v2_tex_2(B_187,A_186)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186)
      | ~ r1_tarski(A_188,u1_struct_0(A_186)) ) ),
    inference(resolution,[status(thm)],[c_14,c_497])).

tff(c_635,plain,(
    ! [A_186,A_9,A_188] :
      ( k9_subset_1(u1_struct_0(A_186),A_9,'#skF_1'(A_186,A_9,A_188)) = A_188
      | ~ r1_tarski(A_188,A_9)
      | ~ v2_tex_2(A_9,A_186)
      | ~ l1_pre_topc(A_186)
      | ~ r1_tarski(A_188,u1_struct_0(A_186))
      | ~ r1_tarski(A_9,u1_struct_0(A_186)) ) ),
    inference(resolution,[status(thm)],[c_14,c_623])).

tff(c_379,plain,(
    ! [A_138,B_139,C_140] :
      ( m1_subset_1('#skF_1'(A_138,B_139,C_140),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ r1_tarski(C_140,B_139)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ v2_tex_2(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [D_47] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_47) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_47,'#skF_3')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_399,plain,(
    ! [B_139,C_140] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_139,C_140)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_139,C_140),'#skF_3')
      | ~ r1_tarski(C_140,B_139)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_139,'#skF_3')
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_379,c_28])).

tff(c_782,plain,(
    ! [B_203,C_204] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_203,C_204)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_203,C_204),'#skF_3')
      | ~ r1_tarski(C_204,B_203)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_203,'#skF_3')
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_399])).

tff(c_785,plain,(
    ! [A_188] :
      ( k1_tarski('#skF_5') != A_188
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_188),'#skF_3')
      | ~ r1_tarski(A_188,'#skF_4')
      | ~ m1_subset_1(A_188,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_188,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_188,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_782])).

tff(c_798,plain,(
    ! [A_205] :
      ( k1_tarski('#skF_5') != A_205
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_205),'#skF_3')
      | ~ m1_subset_1(A_205,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_205,'#skF_4')
      | ~ r1_tarski(A_205,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_34,c_36,c_34,c_785])).

tff(c_825,plain,(
    ! [A_206] :
      ( k1_tarski('#skF_5') != A_206
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_206),'#skF_3')
      | ~ r1_tarski(A_206,'#skF_4')
      | ~ r1_tarski(A_206,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_798])).

tff(c_833,plain,(
    ! [A_129] :
      ( k1_tarski('#skF_5') != A_129
      | ~ r1_tarski(A_129,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_129,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_360,c_825])).

tff(c_852,plain,(
    ! [A_207] :
      ( k1_tarski('#skF_5') != A_207
      | ~ r1_tarski(A_207,'#skF_4')
      | ~ r1_tarski(A_207,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_34,c_833])).

tff(c_912,plain,(
    ! [A_209] :
      ( k1_tarski('#skF_5') != A_209
      | ~ r1_tarski(A_209,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_89,c_852])).

tff(c_937,plain,(
    ! [A_210] :
      ( k1_tarski(A_210) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_210,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_912])).

tff(c_942,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_30,c_937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.60  
% 3.39/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.60  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.39/1.60  
% 3.39/1.60  %Foreground sorts:
% 3.39/1.60  
% 3.39/1.60  
% 3.39/1.60  %Background operators:
% 3.39/1.60  
% 3.39/1.60  
% 3.39/1.60  %Foreground operators:
% 3.39/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.39/1.60  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.39/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.39/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.39/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.39/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.39/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.60  
% 3.69/1.62  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tex_2)).
% 3.69/1.62  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.69/1.62  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.69/1.62  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.69/1.62  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 3.69/1.62  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.62  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.69/1.62  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.62  tff(c_48, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.69/1.62  tff(c_52, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_48])).
% 3.69/1.62  tff(c_83, plain, (![A_60, C_61, B_62]: (r1_tarski(A_60, C_61) | ~r1_tarski(B_62, C_61) | ~r1_tarski(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.69/1.62  tff(c_89, plain, (![A_60]: (r1_tarski(A_60, u1_struct_0('#skF_3')) | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_83])).
% 3.69/1.62  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.62  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.62  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.69/1.62  tff(c_214, plain, (![A_93, B_94, C_95]: (v3_pre_topc('#skF_1'(A_93, B_94, C_95), A_93) | ~r1_tarski(C_95, B_94) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_93))) | ~v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.69/1.62  tff(c_351, plain, (![A_127, B_128, A_129]: (v3_pre_topc('#skF_1'(A_127, B_128, A_129), A_127) | ~r1_tarski(A_129, B_128) | ~v2_tex_2(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~r1_tarski(A_129, u1_struct_0(A_127)))), inference(resolution, [status(thm)], [c_14, c_214])).
% 3.69/1.62  tff(c_360, plain, (![A_127, A_9, A_129]: (v3_pre_topc('#skF_1'(A_127, A_9, A_129), A_127) | ~r1_tarski(A_129, A_9) | ~v2_tex_2(A_9, A_127) | ~l1_pre_topc(A_127) | ~r1_tarski(A_129, u1_struct_0(A_127)) | ~r1_tarski(A_9, u1_struct_0(A_127)))), inference(resolution, [status(thm)], [c_14, c_351])).
% 3.69/1.62  tff(c_497, plain, (![A_164, B_165, C_166]: (k9_subset_1(u1_struct_0(A_164), B_165, '#skF_1'(A_164, B_165, C_166))=C_166 | ~r1_tarski(C_166, B_165) | ~m1_subset_1(C_166, k1_zfmisc_1(u1_struct_0(A_164))) | ~v2_tex_2(B_165, A_164) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.69/1.62  tff(c_623, plain, (![A_186, B_187, A_188]: (k9_subset_1(u1_struct_0(A_186), B_187, '#skF_1'(A_186, B_187, A_188))=A_188 | ~r1_tarski(A_188, B_187) | ~v2_tex_2(B_187, A_186) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186) | ~r1_tarski(A_188, u1_struct_0(A_186)))), inference(resolution, [status(thm)], [c_14, c_497])).
% 3.69/1.62  tff(c_635, plain, (![A_186, A_9, A_188]: (k9_subset_1(u1_struct_0(A_186), A_9, '#skF_1'(A_186, A_9, A_188))=A_188 | ~r1_tarski(A_188, A_9) | ~v2_tex_2(A_9, A_186) | ~l1_pre_topc(A_186) | ~r1_tarski(A_188, u1_struct_0(A_186)) | ~r1_tarski(A_9, u1_struct_0(A_186)))), inference(resolution, [status(thm)], [c_14, c_623])).
% 3.69/1.62  tff(c_379, plain, (![A_138, B_139, C_140]: (m1_subset_1('#skF_1'(A_138, B_139, C_140), k1_zfmisc_1(u1_struct_0(A_138))) | ~r1_tarski(C_140, B_139) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_138))) | ~v2_tex_2(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.69/1.62  tff(c_28, plain, (![D_47]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_47)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_47, '#skF_3') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.62  tff(c_399, plain, (![B_139, C_140]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_139, C_140))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_139, C_140), '#skF_3') | ~r1_tarski(C_140, B_139) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_139, '#skF_3') | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_379, c_28])).
% 3.69/1.62  tff(c_782, plain, (![B_203, C_204]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_203, C_204))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_203, C_204), '#skF_3') | ~r1_tarski(C_204, B_203) | ~m1_subset_1(C_204, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_203, '#skF_3') | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_399])).
% 3.69/1.62  tff(c_785, plain, (![A_188]: (k1_tarski('#skF_5')!=A_188 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_188), '#skF_3') | ~r1_tarski(A_188, '#skF_4') | ~m1_subset_1(A_188, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_188, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_188, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_635, c_782])).
% 3.69/1.62  tff(c_798, plain, (![A_205]: (k1_tarski('#skF_5')!=A_205 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_205), '#skF_3') | ~m1_subset_1(A_205, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_205, '#skF_4') | ~r1_tarski(A_205, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_34, c_36, c_34, c_785])).
% 3.69/1.62  tff(c_825, plain, (![A_206]: (k1_tarski('#skF_5')!=A_206 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_206), '#skF_3') | ~r1_tarski(A_206, '#skF_4') | ~r1_tarski(A_206, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_798])).
% 3.69/1.62  tff(c_833, plain, (![A_129]: (k1_tarski('#skF_5')!=A_129 | ~r1_tarski(A_129, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_129, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_360, c_825])).
% 3.69/1.62  tff(c_852, plain, (![A_207]: (k1_tarski('#skF_5')!=A_207 | ~r1_tarski(A_207, '#skF_4') | ~r1_tarski(A_207, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_34, c_833])).
% 3.69/1.62  tff(c_912, plain, (![A_209]: (k1_tarski('#skF_5')!=A_209 | ~r1_tarski(A_209, '#skF_4'))), inference(resolution, [status(thm)], [c_89, c_852])).
% 3.69/1.62  tff(c_937, plain, (![A_210]: (k1_tarski(A_210)!=k1_tarski('#skF_5') | ~r2_hidden(A_210, '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_912])).
% 3.69/1.62  tff(c_942, plain, $false, inference(resolution, [status(thm)], [c_30, c_937])).
% 3.69/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.62  
% 3.69/1.62  Inference rules
% 3.69/1.62  ----------------------
% 3.69/1.62  #Ref     : 0
% 3.69/1.62  #Sup     : 189
% 3.69/1.62  #Fact    : 0
% 3.69/1.62  #Define  : 0
% 3.69/1.62  #Split   : 2
% 3.69/1.62  #Chain   : 0
% 3.69/1.62  #Close   : 0
% 3.69/1.62  
% 3.69/1.62  Ordering : KBO
% 3.69/1.62  
% 3.69/1.62  Simplification rules
% 3.69/1.62  ----------------------
% 3.69/1.62  #Subsume      : 29
% 3.69/1.62  #Demod        : 88
% 3.69/1.62  #Tautology    : 25
% 3.69/1.62  #SimpNegUnit  : 0
% 3.69/1.62  #BackRed      : 0
% 3.69/1.62  
% 3.69/1.62  #Partial instantiations: 0
% 3.69/1.62  #Strategies tried      : 1
% 3.69/1.62  
% 3.69/1.62  Timing (in seconds)
% 3.69/1.62  ----------------------
% 3.69/1.62  Preprocessing        : 0.34
% 3.69/1.62  Parsing              : 0.18
% 3.69/1.62  CNF conversion       : 0.03
% 3.69/1.62  Main loop            : 0.51
% 3.69/1.62  Inferencing          : 0.18
% 3.69/1.62  Reduction            : 0.12
% 3.69/1.62  Demodulation         : 0.08
% 3.69/1.62  BG Simplification    : 0.02
% 3.69/1.62  Subsumption          : 0.15
% 3.69/1.62  Abstraction          : 0.02
% 3.69/1.62  MUC search           : 0.00
% 3.69/1.62  Cooper               : 0.00
% 3.69/1.62  Total                : 0.88
% 3.69/1.62  Index Insertion      : 0.00
% 3.69/1.62  Index Deletion       : 0.00
% 3.69/1.62  Index Matching       : 0.00
% 3.69/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
