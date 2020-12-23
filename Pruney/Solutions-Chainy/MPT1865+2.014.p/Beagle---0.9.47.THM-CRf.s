%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:19 EST 2020

% Result     : Theorem 7.00s
% Output     : CNFRefutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 131 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 388 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
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
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_65,axiom,(
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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_42])).

tff(c_78,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_89,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(resolution,[status(thm)],[c_84,c_8])).

tff(c_32,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_75,B_76,B_77] :
      ( r2_hidden('#skF_1'(A_75,B_76),B_77)
      | ~ r1_tarski(A_75,B_77)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [A_84,B_85,B_86,B_87] :
      ( r2_hidden('#skF_1'(A_84,B_85),B_86)
      | ~ r1_tarski(B_87,B_86)
      | ~ r1_tarski(A_84,B_87)
      | r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_274,plain,(
    ! [A_99,B_100,B_101,A_102] :
      ( r2_hidden('#skF_1'(A_99,B_100),B_101)
      | ~ r1_tarski(A_99,k1_tarski(A_102))
      | r1_tarski(A_99,B_100)
      | ~ r2_hidden(A_102,B_101) ) ),
    inference(resolution,[status(thm)],[c_10,c_178])).

tff(c_527,plain,(
    ! [A_142,B_143,B_144,A_145] :
      ( r2_hidden('#skF_1'(k1_tarski(A_142),B_143),B_144)
      | r1_tarski(k1_tarski(A_142),B_143)
      | ~ r2_hidden(A_145,B_144)
      | ~ r2_hidden(A_142,k1_tarski(A_145)) ) ),
    inference(resolution,[status(thm)],[c_10,c_274])).

tff(c_564,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_1'(k1_tarski(A_146),B_147),'#skF_5')
      | r1_tarski(k1_tarski(A_146),B_147)
      | ~ r2_hidden(A_146,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_32,c_527])).

tff(c_582,plain,(
    ! [A_151] :
      ( r1_tarski(k1_tarski(A_151),'#skF_5')
      | ~ r2_hidden(A_151,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_564,c_4])).

tff(c_611,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_582])).

tff(c_668,plain,(
    ! [B_154] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_6'),B_154)),'#skF_5')
      | r1_tarski(k1_tarski('#skF_6'),B_154) ) ),
    inference(resolution,[status(thm)],[c_6,c_582])).

tff(c_715,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_6'),B_155),'#skF_5')
      | r1_tarski(k1_tarski('#skF_6'),B_155) ) ),
    inference(resolution,[status(thm)],[c_668,c_8])).

tff(c_993,plain,(
    ! [B_174,B_175] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_6'),B_174),B_175)
      | ~ r1_tarski('#skF_5',B_175)
      | r1_tarski(k1_tarski('#skF_6'),B_174) ) ),
    inference(resolution,[status(thm)],[c_715,c_2])).

tff(c_1022,plain,(
    ! [B_175] :
      ( ~ r1_tarski('#skF_5',B_175)
      | r1_tarski(k1_tarski('#skF_6'),B_175) ) ),
    inference(resolution,[status(thm)],[c_993,c_4])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_335,plain,(
    ! [A_110,B_111,C_112] :
      ( v4_pre_topc('#skF_2'(A_110,B_111,C_112),A_110)
      | ~ r1_tarski(C_112,B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ v2_tex_2(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1305,plain,(
    ! [A_195,B_196,A_197] :
      ( v4_pre_topc('#skF_2'(A_195,B_196,A_197),A_195)
      | ~ r1_tarski(A_197,B_196)
      | ~ v2_tex_2(B_196,A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195)
      | ~ r1_tarski(A_197,u1_struct_0(A_195)) ) ),
    inference(resolution,[status(thm)],[c_16,c_335])).

tff(c_1317,plain,(
    ! [A_197] :
      ( v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_197),'#skF_4')
      | ~ r1_tarski(A_197,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_197,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1305])).

tff(c_1324,plain,(
    ! [A_197] :
      ( v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_197),'#skF_4')
      | ~ r1_tarski(A_197,'#skF_5')
      | ~ r1_tarski(A_197,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1317])).

tff(c_747,plain,(
    ! [A_157,B_158,C_159] :
      ( k9_subset_1(u1_struct_0(A_157),B_158,'#skF_2'(A_157,B_158,C_159)) = C_159
      | ~ r1_tarski(C_159,B_158)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ v2_tex_2(B_158,A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2278,plain,(
    ! [A_265,B_266,A_267] :
      ( k9_subset_1(u1_struct_0(A_265),B_266,'#skF_2'(A_265,B_266,A_267)) = A_267
      | ~ r1_tarski(A_267,B_266)
      | ~ v2_tex_2(B_266,A_265)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265)
      | ~ r1_tarski(A_267,u1_struct_0(A_265)) ) ),
    inference(resolution,[status(thm)],[c_16,c_747])).

tff(c_2290,plain,(
    ! [A_267] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_267)) = A_267
      | ~ r1_tarski(A_267,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_267,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_2278])).

tff(c_2298,plain,(
    ! [A_268] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_268)) = A_268
      | ~ r1_tarski(A_268,'#skF_5')
      | ~ r1_tarski(A_268,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_2290])).

tff(c_435,plain,(
    ! [A_128,B_129,C_130] :
      ( m1_subset_1('#skF_2'(A_128,B_129,C_130),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ r1_tarski(C_130,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v2_tex_2(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [D_48] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',D_48) != k1_tarski('#skF_6')
      | ~ v4_pre_topc(D_48,'#skF_4')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_443,plain,(
    ! [B_129,C_130] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_129,C_130)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4',B_129,C_130),'#skF_4')
      | ~ r1_tarski(C_130,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_129,'#skF_4')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_435,c_30])).

tff(c_451,plain,(
    ! [B_129,C_130] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_129,C_130)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4',B_129,C_130),'#skF_4')
      | ~ r1_tarski(C_130,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_129,'#skF_4')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_443])).

tff(c_2303,plain,(
    ! [A_268] :
      ( k1_tarski('#skF_6') != A_268
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_268),'#skF_4')
      | ~ r1_tarski(A_268,'#skF_5')
      | ~ m1_subset_1(A_268,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_268,'#skF_5')
      | ~ r1_tarski(A_268,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2298,c_451])).

tff(c_4003,plain,(
    ! [A_415] :
      ( k1_tarski('#skF_6') != A_415
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_415),'#skF_4')
      | ~ m1_subset_1(A_415,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_415,'#skF_5')
      | ~ r1_tarski(A_415,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2303])).

tff(c_4035,plain,(
    ! [A_416] :
      ( k1_tarski('#skF_6') != A_416
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_416),'#skF_4')
      | ~ r1_tarski(A_416,'#skF_5')
      | ~ r1_tarski(A_416,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16,c_4003])).

tff(c_4083,plain,(
    ! [A_420] :
      ( k1_tarski('#skF_6') != A_420
      | ~ r1_tarski(A_420,'#skF_5')
      | ~ r1_tarski(A_420,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1324,c_4035])).

tff(c_4123,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1022,c_4083])).

tff(c_4179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_611,c_4123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:26:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.00/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.40  
% 7.08/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.41  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_1
% 7.08/2.41  
% 7.08/2.41  %Foreground sorts:
% 7.08/2.41  
% 7.08/2.41  
% 7.08/2.41  %Background operators:
% 7.08/2.41  
% 7.08/2.41  
% 7.08/2.41  %Foreground operators:
% 7.08/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.08/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.08/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.08/2.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.08/2.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.08/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.08/2.41  tff('#skF_5', type, '#skF_5': $i).
% 7.08/2.41  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.08/2.41  tff('#skF_6', type, '#skF_6': $i).
% 7.08/2.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.08/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.08/2.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.08/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.08/2.41  tff('#skF_4', type, '#skF_4': $i).
% 7.08/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.08/2.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.08/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.08/2.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.08/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.08/2.41  
% 7.17/2.42  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 7.17/2.42  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.17/2.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.17/2.42  tff(f_36, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 7.17/2.42  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 7.17/2.42  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.17/2.42  tff(c_42, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.17/2.42  tff(c_46, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_42])).
% 7.17/2.42  tff(c_78, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.17/2.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.17/2.42  tff(c_84, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_78, c_4])).
% 7.17/2.42  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.17/2.42  tff(c_89, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_84, c_8])).
% 7.17/2.42  tff(c_32, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.17/2.42  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.17/2.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.17/2.42  tff(c_90, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.17/2.42  tff(c_129, plain, (![A_75, B_76, B_77]: (r2_hidden('#skF_1'(A_75, B_76), B_77) | ~r1_tarski(A_75, B_77) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_6, c_90])).
% 7.17/2.42  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.17/2.42  tff(c_178, plain, (![A_84, B_85, B_86, B_87]: (r2_hidden('#skF_1'(A_84, B_85), B_86) | ~r1_tarski(B_87, B_86) | ~r1_tarski(A_84, B_87) | r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_129, c_2])).
% 7.17/2.42  tff(c_274, plain, (![A_99, B_100, B_101, A_102]: (r2_hidden('#skF_1'(A_99, B_100), B_101) | ~r1_tarski(A_99, k1_tarski(A_102)) | r1_tarski(A_99, B_100) | ~r2_hidden(A_102, B_101))), inference(resolution, [status(thm)], [c_10, c_178])).
% 7.17/2.42  tff(c_527, plain, (![A_142, B_143, B_144, A_145]: (r2_hidden('#skF_1'(k1_tarski(A_142), B_143), B_144) | r1_tarski(k1_tarski(A_142), B_143) | ~r2_hidden(A_145, B_144) | ~r2_hidden(A_142, k1_tarski(A_145)))), inference(resolution, [status(thm)], [c_10, c_274])).
% 7.17/2.42  tff(c_564, plain, (![A_146, B_147]: (r2_hidden('#skF_1'(k1_tarski(A_146), B_147), '#skF_5') | r1_tarski(k1_tarski(A_146), B_147) | ~r2_hidden(A_146, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_32, c_527])).
% 7.17/2.42  tff(c_582, plain, (![A_151]: (r1_tarski(k1_tarski(A_151), '#skF_5') | ~r2_hidden(A_151, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_564, c_4])).
% 7.17/2.42  tff(c_611, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_89, c_582])).
% 7.17/2.42  tff(c_668, plain, (![B_154]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_6'), B_154)), '#skF_5') | r1_tarski(k1_tarski('#skF_6'), B_154))), inference(resolution, [status(thm)], [c_6, c_582])).
% 7.17/2.42  tff(c_715, plain, (![B_155]: (r2_hidden('#skF_1'(k1_tarski('#skF_6'), B_155), '#skF_5') | r1_tarski(k1_tarski('#skF_6'), B_155))), inference(resolution, [status(thm)], [c_668, c_8])).
% 7.17/2.42  tff(c_993, plain, (![B_174, B_175]: (r2_hidden('#skF_1'(k1_tarski('#skF_6'), B_174), B_175) | ~r1_tarski('#skF_5', B_175) | r1_tarski(k1_tarski('#skF_6'), B_174))), inference(resolution, [status(thm)], [c_715, c_2])).
% 7.17/2.42  tff(c_1022, plain, (![B_175]: (~r1_tarski('#skF_5', B_175) | r1_tarski(k1_tarski('#skF_6'), B_175))), inference(resolution, [status(thm)], [c_993, c_4])).
% 7.17/2.42  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.17/2.42  tff(c_36, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.17/2.42  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.17/2.42  tff(c_335, plain, (![A_110, B_111, C_112]: (v4_pre_topc('#skF_2'(A_110, B_111, C_112), A_110) | ~r1_tarski(C_112, B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_110))) | ~v2_tex_2(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.17/2.42  tff(c_1305, plain, (![A_195, B_196, A_197]: (v4_pre_topc('#skF_2'(A_195, B_196, A_197), A_195) | ~r1_tarski(A_197, B_196) | ~v2_tex_2(B_196, A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195) | ~r1_tarski(A_197, u1_struct_0(A_195)))), inference(resolution, [status(thm)], [c_16, c_335])).
% 7.17/2.42  tff(c_1317, plain, (![A_197]: (v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_197), '#skF_4') | ~r1_tarski(A_197, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_197, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_1305])).
% 7.17/2.42  tff(c_1324, plain, (![A_197]: (v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_197), '#skF_4') | ~r1_tarski(A_197, '#skF_5') | ~r1_tarski(A_197, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1317])).
% 7.17/2.42  tff(c_747, plain, (![A_157, B_158, C_159]: (k9_subset_1(u1_struct_0(A_157), B_158, '#skF_2'(A_157, B_158, C_159))=C_159 | ~r1_tarski(C_159, B_158) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(A_157))) | ~v2_tex_2(B_158, A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.17/2.42  tff(c_2278, plain, (![A_265, B_266, A_267]: (k9_subset_1(u1_struct_0(A_265), B_266, '#skF_2'(A_265, B_266, A_267))=A_267 | ~r1_tarski(A_267, B_266) | ~v2_tex_2(B_266, A_265) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265) | ~r1_tarski(A_267, u1_struct_0(A_265)))), inference(resolution, [status(thm)], [c_16, c_747])).
% 7.17/2.42  tff(c_2290, plain, (![A_267]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_267))=A_267 | ~r1_tarski(A_267, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_267, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_2278])).
% 7.17/2.42  tff(c_2298, plain, (![A_268]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_268))=A_268 | ~r1_tarski(A_268, '#skF_5') | ~r1_tarski(A_268, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_2290])).
% 7.17/2.42  tff(c_435, plain, (![A_128, B_129, C_130]: (m1_subset_1('#skF_2'(A_128, B_129, C_130), k1_zfmisc_1(u1_struct_0(A_128))) | ~r1_tarski(C_130, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_128))) | ~v2_tex_2(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.17/2.42  tff(c_30, plain, (![D_48]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', D_48)!=k1_tarski('#skF_6') | ~v4_pre_topc(D_48, '#skF_4') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.17/2.42  tff(c_443, plain, (![B_129, C_130]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_129, C_130))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', B_129, C_130), '#skF_4') | ~r1_tarski(C_130, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_129, '#skF_4') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_435, c_30])).
% 7.17/2.42  tff(c_451, plain, (![B_129, C_130]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_129, C_130))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', B_129, C_130), '#skF_4') | ~r1_tarski(C_130, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_129, '#skF_4') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_443])).
% 7.17/2.42  tff(c_2303, plain, (![A_268]: (k1_tarski('#skF_6')!=A_268 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_268), '#skF_4') | ~r1_tarski(A_268, '#skF_5') | ~m1_subset_1(A_268, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_268, '#skF_5') | ~r1_tarski(A_268, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2298, c_451])).
% 7.17/2.42  tff(c_4003, plain, (![A_415]: (k1_tarski('#skF_6')!=A_415 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_415), '#skF_4') | ~m1_subset_1(A_415, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_415, '#skF_5') | ~r1_tarski(A_415, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2303])).
% 7.17/2.42  tff(c_4035, plain, (![A_416]: (k1_tarski('#skF_6')!=A_416 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_416), '#skF_4') | ~r1_tarski(A_416, '#skF_5') | ~r1_tarski(A_416, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_16, c_4003])).
% 7.17/2.42  tff(c_4083, plain, (![A_420]: (k1_tarski('#skF_6')!=A_420 | ~r1_tarski(A_420, '#skF_5') | ~r1_tarski(A_420, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1324, c_4035])).
% 7.17/2.42  tff(c_4123, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1022, c_4083])).
% 7.17/2.42  tff(c_4179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_611, c_4123])).
% 7.17/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.17/2.42  
% 7.17/2.42  Inference rules
% 7.17/2.42  ----------------------
% 7.17/2.42  #Ref     : 0
% 7.17/2.42  #Sup     : 1045
% 7.17/2.42  #Fact    : 0
% 7.17/2.42  #Define  : 0
% 7.17/2.42  #Split   : 6
% 7.17/2.42  #Chain   : 0
% 7.17/2.42  #Close   : 0
% 7.17/2.42  
% 7.17/2.42  Ordering : KBO
% 7.17/2.42  
% 7.17/2.42  Simplification rules
% 7.17/2.42  ----------------------
% 7.17/2.42  #Subsume      : 409
% 7.17/2.42  #Demod        : 215
% 7.17/2.42  #Tautology    : 75
% 7.17/2.42  #SimpNegUnit  : 0
% 7.17/2.42  #BackRed      : 0
% 7.17/2.42  
% 7.17/2.42  #Partial instantiations: 0
% 7.17/2.42  #Strategies tried      : 1
% 7.17/2.42  
% 7.17/2.42  Timing (in seconds)
% 7.17/2.42  ----------------------
% 7.17/2.43  Preprocessing        : 0.30
% 7.17/2.43  Parsing              : 0.16
% 7.17/2.43  CNF conversion       : 0.03
% 7.17/2.43  Main loop            : 1.37
% 7.17/2.43  Inferencing          : 0.39
% 7.17/2.43  Reduction            : 0.33
% 7.17/2.43  Demodulation         : 0.22
% 7.17/2.43  BG Simplification    : 0.04
% 7.17/2.43  Subsumption          : 0.52
% 7.17/2.43  Abstraction          : 0.05
% 7.17/2.43  MUC search           : 0.00
% 7.17/2.43  Cooper               : 0.00
% 7.17/2.43  Total                : 1.71
% 7.17/2.43  Index Insertion      : 0.00
% 7.17/2.43  Index Deletion       : 0.00
% 7.17/2.43  Index Matching       : 0.00
% 7.17/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
