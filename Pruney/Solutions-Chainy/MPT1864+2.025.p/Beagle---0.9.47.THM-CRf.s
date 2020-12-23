%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:17 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   55 (  91 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 276 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

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

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_75,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k1_tarski(A_56),k1_zfmisc_1(B_57))
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tarski(A_56),B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_75,c_10])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_46])).

tff(c_86,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(A_60,C_61)
      | ~ r1_tarski(B_62,C_61)
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,(
    ! [A_94,B_95,C_96] :
      ( v3_pre_topc('#skF_1'(A_94,B_95,C_96),A_94)
      | ~ r1_tarski(C_96,B_95)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v2_tex_2(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_490,plain,(
    ! [A_151,B_152,A_153] :
      ( v3_pre_topc('#skF_1'(A_151,B_152,A_153),A_151)
      | ~ r1_tarski(A_153,B_152)
      | ~ v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ r1_tarski(A_153,u1_struct_0(A_151)) ) ),
    inference(resolution,[status(thm)],[c_12,c_219])).

tff(c_506,plain,(
    ! [A_151,A_9,A_153] :
      ( v3_pre_topc('#skF_1'(A_151,A_9,A_153),A_151)
      | ~ r1_tarski(A_153,A_9)
      | ~ v2_tex_2(A_9,A_151)
      | ~ l1_pre_topc(A_151)
      | ~ r1_tarski(A_153,u1_struct_0(A_151))
      | ~ r1_tarski(A_9,u1_struct_0(A_151)) ) ),
    inference(resolution,[status(thm)],[c_12,c_490])).

tff(c_533,plain,(
    ! [A_165,B_166,C_167] :
      ( k9_subset_1(u1_struct_0(A_165),B_166,'#skF_1'(A_165,B_166,C_167)) = C_167
      | ~ r1_tarski(C_167,B_166)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ v2_tex_2(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_858,plain,(
    ! [A_242,B_243,A_244] :
      ( k9_subset_1(u1_struct_0(A_242),B_243,'#skF_1'(A_242,B_243,A_244)) = A_244
      | ~ r1_tarski(A_244,B_243)
      | ~ v2_tex_2(B_243,A_242)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242)
      | ~ r1_tarski(A_244,u1_struct_0(A_242)) ) ),
    inference(resolution,[status(thm)],[c_12,c_533])).

tff(c_874,plain,(
    ! [A_242,A_9,A_244] :
      ( k9_subset_1(u1_struct_0(A_242),A_9,'#skF_1'(A_242,A_9,A_244)) = A_244
      | ~ r1_tarski(A_244,A_9)
      | ~ v2_tex_2(A_9,A_242)
      | ~ l1_pre_topc(A_242)
      | ~ r1_tarski(A_244,u1_struct_0(A_242))
      | ~ r1_tarski(A_9,u1_struct_0(A_242)) ) ),
    inference(resolution,[status(thm)],[c_12,c_858])).

tff(c_374,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1('#skF_1'(A_115,B_116,C_117),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ r1_tarski(C_117,B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v2_tex_2(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [D_47] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_47) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_47,'#skF_3')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_390,plain,(
    ! [B_116,C_117] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_116,C_117)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_116,C_117),'#skF_3')
      | ~ r1_tarski(C_117,B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_116,'#skF_3')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_374,c_26])).

tff(c_1124,plain,(
    ! [B_268,C_269] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_268,C_269)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_268,C_269),'#skF_3')
      | ~ r1_tarski(C_269,B_268)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_268,'#skF_3')
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_390])).

tff(c_1130,plain,(
    ! [A_244] :
      ( k1_tarski('#skF_5') != A_244
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_244),'#skF_3')
      | ~ r1_tarski(A_244,'#skF_4')
      | ~ m1_subset_1(A_244,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_244,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_244,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_1124])).

tff(c_1145,plain,(
    ! [A_270] :
      ( k1_tarski('#skF_5') != A_270
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_270),'#skF_3')
      | ~ m1_subset_1(A_270,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_270,'#skF_4')
      | ~ r1_tarski(A_270,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36,c_32,c_34,c_32,c_1130])).

tff(c_1177,plain,(
    ! [A_271] :
      ( k1_tarski('#skF_5') != A_271
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_271),'#skF_3')
      | ~ r1_tarski(A_271,'#skF_4')
      | ~ r1_tarski(A_271,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1145])).

tff(c_1185,plain,(
    ! [A_153] :
      ( k1_tarski('#skF_5') != A_153
      | ~ r1_tarski(A_153,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_153,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_506,c_1177])).

tff(c_1204,plain,(
    ! [A_272] :
      ( k1_tarski('#skF_5') != A_272
      | ~ r1_tarski(A_272,'#skF_4')
      | ~ r1_tarski(A_272,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36,c_32,c_1185])).

tff(c_1272,plain,(
    ! [A_273] :
      ( k1_tarski('#skF_5') != A_273
      | ~ r1_tarski(A_273,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_1204])).

tff(c_1306,plain,(
    ! [A_274] :
      ( k1_tarski(A_274) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_274,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_84,c_1272])).

tff(c_1311,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28,c_1306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.87  
% 4.56/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.88  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.56/1.88  
% 4.56/1.88  %Foreground sorts:
% 4.56/1.88  
% 4.56/1.88  
% 4.56/1.88  %Background operators:
% 4.56/1.88  
% 4.56/1.88  
% 4.56/1.88  %Foreground operators:
% 4.56/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.56/1.88  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.56/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.56/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.56/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.56/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.56/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.56/1.88  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.56/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.56/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.56/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.56/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.56/1.88  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.56/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/1.88  
% 4.56/1.89  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 4.56/1.89  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.56/1.89  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.56/1.89  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.56/1.89  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 4.56/1.89  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.56/1.89  tff(c_75, plain, (![A_56, B_57]: (m1_subset_1(k1_tarski(A_56), k1_zfmisc_1(B_57)) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.89  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.89  tff(c_84, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), B_57) | ~r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_75, c_10])).
% 4.56/1.89  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.56/1.89  tff(c_46, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.89  tff(c_50, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_46])).
% 4.56/1.89  tff(c_86, plain, (![A_60, C_61, B_62]: (r1_tarski(A_60, C_61) | ~r1_tarski(B_62, C_61) | ~r1_tarski(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.89  tff(c_92, plain, (![A_60]: (r1_tarski(A_60, u1_struct_0('#skF_3')) | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 4.56/1.89  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.56/1.89  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.56/1.89  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.89  tff(c_219, plain, (![A_94, B_95, C_96]: (v3_pre_topc('#skF_1'(A_94, B_95, C_96), A_94) | ~r1_tarski(C_96, B_95) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_94))) | ~v2_tex_2(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.89  tff(c_490, plain, (![A_151, B_152, A_153]: (v3_pre_topc('#skF_1'(A_151, B_152, A_153), A_151) | ~r1_tarski(A_153, B_152) | ~v2_tex_2(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~r1_tarski(A_153, u1_struct_0(A_151)))), inference(resolution, [status(thm)], [c_12, c_219])).
% 4.56/1.89  tff(c_506, plain, (![A_151, A_9, A_153]: (v3_pre_topc('#skF_1'(A_151, A_9, A_153), A_151) | ~r1_tarski(A_153, A_9) | ~v2_tex_2(A_9, A_151) | ~l1_pre_topc(A_151) | ~r1_tarski(A_153, u1_struct_0(A_151)) | ~r1_tarski(A_9, u1_struct_0(A_151)))), inference(resolution, [status(thm)], [c_12, c_490])).
% 4.56/1.89  tff(c_533, plain, (![A_165, B_166, C_167]: (k9_subset_1(u1_struct_0(A_165), B_166, '#skF_1'(A_165, B_166, C_167))=C_167 | ~r1_tarski(C_167, B_166) | ~m1_subset_1(C_167, k1_zfmisc_1(u1_struct_0(A_165))) | ~v2_tex_2(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.89  tff(c_858, plain, (![A_242, B_243, A_244]: (k9_subset_1(u1_struct_0(A_242), B_243, '#skF_1'(A_242, B_243, A_244))=A_244 | ~r1_tarski(A_244, B_243) | ~v2_tex_2(B_243, A_242) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242) | ~r1_tarski(A_244, u1_struct_0(A_242)))), inference(resolution, [status(thm)], [c_12, c_533])).
% 4.56/1.89  tff(c_874, plain, (![A_242, A_9, A_244]: (k9_subset_1(u1_struct_0(A_242), A_9, '#skF_1'(A_242, A_9, A_244))=A_244 | ~r1_tarski(A_244, A_9) | ~v2_tex_2(A_9, A_242) | ~l1_pre_topc(A_242) | ~r1_tarski(A_244, u1_struct_0(A_242)) | ~r1_tarski(A_9, u1_struct_0(A_242)))), inference(resolution, [status(thm)], [c_12, c_858])).
% 4.56/1.89  tff(c_374, plain, (![A_115, B_116, C_117]: (m1_subset_1('#skF_1'(A_115, B_116, C_117), k1_zfmisc_1(u1_struct_0(A_115))) | ~r1_tarski(C_117, B_116) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_115))) | ~v2_tex_2(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.89  tff(c_26, plain, (![D_47]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_47)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_47, '#skF_3') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.56/1.89  tff(c_390, plain, (![B_116, C_117]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_116, C_117))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_116, C_117), '#skF_3') | ~r1_tarski(C_117, B_116) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_116, '#skF_3') | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_374, c_26])).
% 4.56/1.89  tff(c_1124, plain, (![B_268, C_269]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_268, C_269))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_268, C_269), '#skF_3') | ~r1_tarski(C_269, B_268) | ~m1_subset_1(C_269, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_268, '#skF_3') | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_390])).
% 4.56/1.89  tff(c_1130, plain, (![A_244]: (k1_tarski('#skF_5')!=A_244 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_244), '#skF_3') | ~r1_tarski(A_244, '#skF_4') | ~m1_subset_1(A_244, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_244, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_244, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_874, c_1124])).
% 4.56/1.89  tff(c_1145, plain, (![A_270]: (k1_tarski('#skF_5')!=A_270 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_270), '#skF_3') | ~m1_subset_1(A_270, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_270, '#skF_4') | ~r1_tarski(A_270, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36, c_32, c_34, c_32, c_1130])).
% 4.56/1.89  tff(c_1177, plain, (![A_271]: (k1_tarski('#skF_5')!=A_271 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_271), '#skF_3') | ~r1_tarski(A_271, '#skF_4') | ~r1_tarski(A_271, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_1145])).
% 4.56/1.89  tff(c_1185, plain, (![A_153]: (k1_tarski('#skF_5')!=A_153 | ~r1_tarski(A_153, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_153, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_506, c_1177])).
% 4.56/1.89  tff(c_1204, plain, (![A_272]: (k1_tarski('#skF_5')!=A_272 | ~r1_tarski(A_272, '#skF_4') | ~r1_tarski(A_272, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36, c_32, c_1185])).
% 4.56/1.89  tff(c_1272, plain, (![A_273]: (k1_tarski('#skF_5')!=A_273 | ~r1_tarski(A_273, '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_1204])).
% 4.56/1.89  tff(c_1306, plain, (![A_274]: (k1_tarski(A_274)!=k1_tarski('#skF_5') | ~r2_hidden(A_274, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_1272])).
% 4.56/1.89  tff(c_1311, plain, $false, inference(resolution, [status(thm)], [c_28, c_1306])).
% 4.56/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.89  
% 4.56/1.89  Inference rules
% 4.56/1.89  ----------------------
% 4.56/1.89  #Ref     : 0
% 4.56/1.89  #Sup     : 267
% 4.56/1.89  #Fact    : 0
% 4.56/1.89  #Define  : 0
% 4.56/1.89  #Split   : 2
% 4.56/1.89  #Chain   : 0
% 4.56/1.89  #Close   : 0
% 4.56/1.89  
% 4.56/1.89  Ordering : KBO
% 4.56/1.89  
% 4.56/1.89  Simplification rules
% 4.56/1.89  ----------------------
% 4.56/1.89  #Subsume      : 30
% 4.56/1.89  #Demod        : 107
% 4.56/1.89  #Tautology    : 38
% 4.56/1.89  #SimpNegUnit  : 0
% 4.56/1.89  #BackRed      : 0
% 4.56/1.89  
% 4.56/1.89  #Partial instantiations: 0
% 4.56/1.89  #Strategies tried      : 1
% 4.56/1.89  
% 4.56/1.89  Timing (in seconds)
% 4.56/1.89  ----------------------
% 4.56/1.89  Preprocessing        : 0.35
% 4.56/1.89  Parsing              : 0.19
% 4.56/1.89  CNF conversion       : 0.02
% 4.56/1.89  Main loop            : 0.72
% 4.56/1.89  Inferencing          : 0.26
% 4.56/1.89  Reduction            : 0.17
% 4.56/1.89  Demodulation         : 0.11
% 4.56/1.89  BG Simplification    : 0.03
% 4.56/1.89  Subsumption          : 0.22
% 4.56/1.89  Abstraction          : 0.04
% 4.56/1.89  MUC search           : 0.00
% 4.56/1.89  Cooper               : 0.00
% 4.56/1.89  Total                : 1.10
% 4.56/1.89  Index Insertion      : 0.00
% 4.56/1.89  Index Deletion       : 0.00
% 4.56/1.89  Index Matching       : 0.00
% 4.56/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
