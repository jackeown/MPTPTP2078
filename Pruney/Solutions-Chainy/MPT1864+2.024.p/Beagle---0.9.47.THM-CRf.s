%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:17 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   55 (  90 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  138 ( 277 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(k2_tarski(A_65,B_66),C_67)
      | ~ r2_hidden(B_66,C_67)
      | ~ r2_hidden(A_65,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [A_4,C_67] :
      ( r1_tarski(k1_tarski(A_4),C_67)
      | ~ r2_hidden(A_4,C_67)
      | ~ r2_hidden(A_4,C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_77,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(A_61,C_62)
      | ~ r1_tarski(B_63,C_62)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_77])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_371,plain,(
    ! [A_131,B_132,C_133] :
      ( v3_pre_topc('#skF_1'(A_131,B_132,C_133),A_131)
      | ~ r1_tarski(C_133,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v2_tex_2(B_132,A_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_577,plain,(
    ! [A_196,B_197,A_198] :
      ( v3_pre_topc('#skF_1'(A_196,B_197,A_198),A_196)
      | ~ r1_tarski(A_198,B_197)
      | ~ v2_tex_2(B_197,A_196)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196)
      | ~ r1_tarski(A_198,u1_struct_0(A_196)) ) ),
    inference(resolution,[status(thm)],[c_14,c_371])).

tff(c_589,plain,(
    ! [A_196,A_8,A_198] :
      ( v3_pre_topc('#skF_1'(A_196,A_8,A_198),A_196)
      | ~ r1_tarski(A_198,A_8)
      | ~ v2_tex_2(A_8,A_196)
      | ~ l1_pre_topc(A_196)
      | ~ r1_tarski(A_198,u1_struct_0(A_196))
      | ~ r1_tarski(A_8,u1_struct_0(A_196)) ) ),
    inference(resolution,[status(thm)],[c_14,c_577])).

tff(c_612,plain,(
    ! [A_207,B_208,C_209] :
      ( k9_subset_1(u1_struct_0(A_207),B_208,'#skF_1'(A_207,B_208,C_209)) = C_209
      | ~ r1_tarski(C_209,B_208)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ v2_tex_2(B_208,A_207)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_826,plain,(
    ! [A_267,B_268,A_269] :
      ( k9_subset_1(u1_struct_0(A_267),B_268,'#skF_1'(A_267,B_268,A_269)) = A_269
      | ~ r1_tarski(A_269,B_268)
      | ~ v2_tex_2(B_268,A_267)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267)
      | ~ r1_tarski(A_269,u1_struct_0(A_267)) ) ),
    inference(resolution,[status(thm)],[c_14,c_612])).

tff(c_838,plain,(
    ! [A_267,A_8,A_269] :
      ( k9_subset_1(u1_struct_0(A_267),A_8,'#skF_1'(A_267,A_8,A_269)) = A_269
      | ~ r1_tarski(A_269,A_8)
      | ~ v2_tex_2(A_8,A_267)
      | ~ l1_pre_topc(A_267)
      | ~ r1_tarski(A_269,u1_struct_0(A_267))
      | ~ r1_tarski(A_8,u1_struct_0(A_267)) ) ),
    inference(resolution,[status(thm)],[c_14,c_826])).

tff(c_517,plain,(
    ! [A_183,B_184,C_185] :
      ( m1_subset_1('#skF_1'(A_183,B_184,C_185),k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ r1_tarski(C_185,B_184)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ v2_tex_2(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [D_46] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_46) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_46,'#skF_3')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_535,plain,(
    ! [B_184,C_185] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_184,C_185)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_184,C_185),'#skF_3')
      | ~ r1_tarski(C_185,B_184)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_184,'#skF_3')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_517,c_28])).

tff(c_978,plain,(
    ! [B_299,C_300] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_299,C_300)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_299,C_300),'#skF_3')
      | ~ r1_tarski(C_300,B_299)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_299,'#skF_3')
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_535])).

tff(c_981,plain,(
    ! [A_269] :
      ( k1_tarski('#skF_5') != A_269
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_269),'#skF_3')
      | ~ r1_tarski(A_269,'#skF_4')
      | ~ m1_subset_1(A_269,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_269,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_269,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_978])).

tff(c_994,plain,(
    ! [A_301] :
      ( k1_tarski('#skF_5') != A_301
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_301),'#skF_3')
      | ~ m1_subset_1(A_301,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_301,'#skF_4')
      | ~ r1_tarski(A_301,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_34,c_36,c_34,c_981])).

tff(c_1021,plain,(
    ! [A_302] :
      ( k1_tarski('#skF_5') != A_302
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_302),'#skF_3')
      | ~ r1_tarski(A_302,'#skF_4')
      | ~ r1_tarski(A_302,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_994])).

tff(c_1029,plain,(
    ! [A_198] :
      ( k1_tarski('#skF_5') != A_198
      | ~ r1_tarski(A_198,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_198,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_589,c_1021])).

tff(c_1048,plain,(
    ! [A_303] :
      ( k1_tarski('#skF_5') != A_303
      | ~ r1_tarski(A_303,'#skF_4')
      | ~ r1_tarski(A_303,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_34,c_1029])).

tff(c_1107,plain,(
    ! [A_304] :
      ( k1_tarski('#skF_5') != A_304
      | ~ r1_tarski(A_304,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_1048])).

tff(c_1132,plain,(
    ! [A_305] :
      ( k1_tarski(A_305) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_305,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_111,c_1107])).

tff(c_1137,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_30,c_1132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.66  
% 3.98/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.66  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.98/1.66  
% 3.98/1.66  %Foreground sorts:
% 3.98/1.66  
% 3.98/1.66  
% 3.98/1.66  %Background operators:
% 3.98/1.66  
% 3.98/1.66  
% 3.98/1.66  %Foreground operators:
% 3.98/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.98/1.66  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.98/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.98/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.98/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.98/1.66  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.98/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.98/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.98/1.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.98/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.66  
% 3.98/1.68  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 3.98/1.68  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.98/1.68  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.98/1.68  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.98/1.68  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.98/1.68  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 3.98/1.68  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.98/1.68  tff(c_4, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.68  tff(c_100, plain, (![A_65, B_66, C_67]: (r1_tarski(k2_tarski(A_65, B_66), C_67) | ~r2_hidden(B_66, C_67) | ~r2_hidden(A_65, C_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.98/1.68  tff(c_111, plain, (![A_4, C_67]: (r1_tarski(k1_tarski(A_4), C_67) | ~r2_hidden(A_4, C_67) | ~r2_hidden(A_4, C_67))), inference(superposition, [status(thm), theory('equality')], [c_4, c_100])).
% 3.98/1.68  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.98/1.68  tff(c_48, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.68  tff(c_52, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_48])).
% 3.98/1.68  tff(c_77, plain, (![A_61, C_62, B_63]: (r1_tarski(A_61, C_62) | ~r1_tarski(B_63, C_62) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.68  tff(c_80, plain, (![A_61]: (r1_tarski(A_61, u1_struct_0('#skF_3')) | ~r1_tarski(A_61, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_77])).
% 3.98/1.68  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.98/1.68  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.98/1.68  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.68  tff(c_371, plain, (![A_131, B_132, C_133]: (v3_pre_topc('#skF_1'(A_131, B_132, C_133), A_131) | ~r1_tarski(C_133, B_132) | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_131))) | ~v2_tex_2(B_132, A_131) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.68  tff(c_577, plain, (![A_196, B_197, A_198]: (v3_pre_topc('#skF_1'(A_196, B_197, A_198), A_196) | ~r1_tarski(A_198, B_197) | ~v2_tex_2(B_197, A_196) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196) | ~r1_tarski(A_198, u1_struct_0(A_196)))), inference(resolution, [status(thm)], [c_14, c_371])).
% 3.98/1.68  tff(c_589, plain, (![A_196, A_8, A_198]: (v3_pre_topc('#skF_1'(A_196, A_8, A_198), A_196) | ~r1_tarski(A_198, A_8) | ~v2_tex_2(A_8, A_196) | ~l1_pre_topc(A_196) | ~r1_tarski(A_198, u1_struct_0(A_196)) | ~r1_tarski(A_8, u1_struct_0(A_196)))), inference(resolution, [status(thm)], [c_14, c_577])).
% 3.98/1.68  tff(c_612, plain, (![A_207, B_208, C_209]: (k9_subset_1(u1_struct_0(A_207), B_208, '#skF_1'(A_207, B_208, C_209))=C_209 | ~r1_tarski(C_209, B_208) | ~m1_subset_1(C_209, k1_zfmisc_1(u1_struct_0(A_207))) | ~v2_tex_2(B_208, A_207) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.68  tff(c_826, plain, (![A_267, B_268, A_269]: (k9_subset_1(u1_struct_0(A_267), B_268, '#skF_1'(A_267, B_268, A_269))=A_269 | ~r1_tarski(A_269, B_268) | ~v2_tex_2(B_268, A_267) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267) | ~r1_tarski(A_269, u1_struct_0(A_267)))), inference(resolution, [status(thm)], [c_14, c_612])).
% 3.98/1.68  tff(c_838, plain, (![A_267, A_8, A_269]: (k9_subset_1(u1_struct_0(A_267), A_8, '#skF_1'(A_267, A_8, A_269))=A_269 | ~r1_tarski(A_269, A_8) | ~v2_tex_2(A_8, A_267) | ~l1_pre_topc(A_267) | ~r1_tarski(A_269, u1_struct_0(A_267)) | ~r1_tarski(A_8, u1_struct_0(A_267)))), inference(resolution, [status(thm)], [c_14, c_826])).
% 3.98/1.68  tff(c_517, plain, (![A_183, B_184, C_185]: (m1_subset_1('#skF_1'(A_183, B_184, C_185), k1_zfmisc_1(u1_struct_0(A_183))) | ~r1_tarski(C_185, B_184) | ~m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0(A_183))) | ~v2_tex_2(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.68  tff(c_28, plain, (![D_46]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_46)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_46, '#skF_3') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.98/1.68  tff(c_535, plain, (![B_184, C_185]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_184, C_185))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_184, C_185), '#skF_3') | ~r1_tarski(C_185, B_184) | ~m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_184, '#skF_3') | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_517, c_28])).
% 3.98/1.68  tff(c_978, plain, (![B_299, C_300]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_299, C_300))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_299, C_300), '#skF_3') | ~r1_tarski(C_300, B_299) | ~m1_subset_1(C_300, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_299, '#skF_3') | ~m1_subset_1(B_299, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_535])).
% 3.98/1.68  tff(c_981, plain, (![A_269]: (k1_tarski('#skF_5')!=A_269 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_269), '#skF_3') | ~r1_tarski(A_269, '#skF_4') | ~m1_subset_1(A_269, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_269, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_269, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_838, c_978])).
% 3.98/1.68  tff(c_994, plain, (![A_301]: (k1_tarski('#skF_5')!=A_301 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_301), '#skF_3') | ~m1_subset_1(A_301, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_301, '#skF_4') | ~r1_tarski(A_301, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_34, c_36, c_34, c_981])).
% 3.98/1.68  tff(c_1021, plain, (![A_302]: (k1_tarski('#skF_5')!=A_302 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_302), '#skF_3') | ~r1_tarski(A_302, '#skF_4') | ~r1_tarski(A_302, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_994])).
% 3.98/1.68  tff(c_1029, plain, (![A_198]: (k1_tarski('#skF_5')!=A_198 | ~r1_tarski(A_198, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_198, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_589, c_1021])).
% 3.98/1.68  tff(c_1048, plain, (![A_303]: (k1_tarski('#skF_5')!=A_303 | ~r1_tarski(A_303, '#skF_4') | ~r1_tarski(A_303, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_34, c_1029])).
% 3.98/1.68  tff(c_1107, plain, (![A_304]: (k1_tarski('#skF_5')!=A_304 | ~r1_tarski(A_304, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_1048])).
% 3.98/1.68  tff(c_1132, plain, (![A_305]: (k1_tarski(A_305)!=k1_tarski('#skF_5') | ~r2_hidden(A_305, '#skF_4'))), inference(resolution, [status(thm)], [c_111, c_1107])).
% 3.98/1.68  tff(c_1137, plain, $false, inference(resolution, [status(thm)], [c_30, c_1132])).
% 3.98/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.68  
% 3.98/1.68  Inference rules
% 3.98/1.68  ----------------------
% 3.98/1.68  #Ref     : 0
% 3.98/1.68  #Sup     : 240
% 3.98/1.68  #Fact    : 0
% 3.98/1.68  #Define  : 0
% 3.98/1.68  #Split   : 4
% 3.98/1.68  #Chain   : 0
% 3.98/1.68  #Close   : 0
% 3.98/1.68  
% 3.98/1.68  Ordering : KBO
% 3.98/1.68  
% 3.98/1.68  Simplification rules
% 3.98/1.68  ----------------------
% 3.98/1.68  #Subsume      : 52
% 3.98/1.68  #Demod        : 95
% 3.98/1.68  #Tautology    : 24
% 3.98/1.68  #SimpNegUnit  : 1
% 3.98/1.68  #BackRed      : 1
% 3.98/1.68  
% 3.98/1.68  #Partial instantiations: 0
% 3.98/1.68  #Strategies tried      : 1
% 3.98/1.68  
% 3.98/1.68  Timing (in seconds)
% 3.98/1.68  ----------------------
% 3.98/1.68  Preprocessing        : 0.31
% 3.98/1.68  Parsing              : 0.16
% 3.98/1.68  CNF conversion       : 0.02
% 3.98/1.68  Main loop            : 0.60
% 3.98/1.68  Inferencing          : 0.21
% 3.98/1.68  Reduction            : 0.14
% 3.98/1.68  Demodulation         : 0.09
% 3.98/1.68  BG Simplification    : 0.02
% 3.98/1.68  Subsumption          : 0.18
% 3.98/1.68  Abstraction          : 0.03
% 3.98/1.68  MUC search           : 0.00
% 3.98/1.68  Cooper               : 0.00
% 3.98/1.68  Total                : 0.94
% 3.98/1.68  Index Insertion      : 0.00
% 3.98/1.68  Index Deletion       : 0.00
% 3.98/1.68  Index Matching       : 0.00
% 3.98/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
