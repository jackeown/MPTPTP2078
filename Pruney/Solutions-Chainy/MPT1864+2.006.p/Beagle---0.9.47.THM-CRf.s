%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:14 EST 2020

% Result     : Theorem 6.60s
% Output     : CNFRefutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 133 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 388 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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
                         => ~ ( v3_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_52])).

tff(c_88,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_69] : r1_tarski(A_69,A_69) ),
    inference(resolution,[status(thm)],[c_88,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | ~ r1_tarski(k1_tarski(A_9),B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(resolution,[status(thm)],[c_101,c_12])).

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden('#skF_1'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [A_85,B_86,B_87,B_88] :
      ( r2_hidden('#skF_1'(A_85,B_86),B_87)
      | ~ r1_tarski(B_88,B_87)
      | ~ r1_tarski(A_85,B_88)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_279,plain,(
    ! [A_100,B_101,B_102,A_103] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(A_100,k1_tarski(A_103))
      | r1_tarski(A_100,B_101)
      | ~ r2_hidden(A_103,B_102) ) ),
    inference(resolution,[status(thm)],[c_14,c_183])).

tff(c_505,plain,(
    ! [A_142,B_143,B_144,A_145] :
      ( r2_hidden('#skF_1'(k1_tarski(A_142),B_143),B_144)
      | r1_tarski(k1_tarski(A_142),B_143)
      | ~ r2_hidden(A_145,B_144)
      | ~ r2_hidden(A_142,k1_tarski(A_145)) ) ),
    inference(resolution,[status(thm)],[c_14,c_279])).

tff(c_542,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_1'(k1_tarski(A_146),B_147),'#skF_5')
      | r1_tarski(k1_tarski(A_146),B_147)
      | ~ r2_hidden(A_146,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_34,c_505])).

tff(c_559,plain,(
    ! [A_148] :
      ( r1_tarski(k1_tarski(A_148),'#skF_5')
      | ~ r2_hidden(A_148,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_542,c_4])).

tff(c_588,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_106,c_559])).

tff(c_647,plain,(
    ! [B_155] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_6'),B_155)),'#skF_5')
      | r1_tarski(k1_tarski('#skF_6'),B_155) ) ),
    inference(resolution,[status(thm)],[c_6,c_559])).

tff(c_694,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_6'),B_156),'#skF_5')
      | r1_tarski(k1_tarski('#skF_6'),B_156) ) ),
    inference(resolution,[status(thm)],[c_647,c_12])).

tff(c_954,plain,(
    ! [B_175,B_176] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_6'),B_175),B_176)
      | ~ r1_tarski('#skF_5',B_176)
      | r1_tarski(k1_tarski('#skF_6'),B_175) ) ),
    inference(resolution,[status(thm)],[c_694,c_2])).

tff(c_983,plain,(
    ! [B_176] :
      ( ~ r1_tarski('#skF_5',B_176)
      | r1_tarski(k1_tarski('#skF_6'),B_176) ) ),
    inference(resolution,[status(thm)],[c_954,c_4])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_340,plain,(
    ! [A_111,B_112,C_113] :
      ( v3_pre_topc('#skF_2'(A_111,B_112,C_113),A_111)
      | ~ r1_tarski(C_113,B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1314,plain,(
    ! [A_198,B_199,A_200] :
      ( v3_pre_topc('#skF_2'(A_198,B_199,A_200),A_198)
      | ~ r1_tarski(A_200,B_199)
      | ~ v2_tex_2(B_199,A_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198)
      | ~ r1_tarski(A_200,u1_struct_0(A_198)) ) ),
    inference(resolution,[status(thm)],[c_18,c_340])).

tff(c_1323,plain,(
    ! [A_200] :
      ( v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_200),'#skF_4')
      | ~ r1_tarski(A_200,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1314])).

tff(c_1329,plain,(
    ! [A_200] :
      ( v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_200),'#skF_4')
      | ~ r1_tarski(A_200,'#skF_5')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_1323])).

tff(c_726,plain,(
    ! [A_158,B_159,C_160] :
      ( k9_subset_1(u1_struct_0(A_158),B_159,'#skF_2'(A_158,B_159,C_160)) = C_160
      | ~ r1_tarski(C_160,B_159)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ v2_tex_2(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2050,plain,(
    ! [A_256,B_257,A_258] :
      ( k9_subset_1(u1_struct_0(A_256),B_257,'#skF_2'(A_256,B_257,A_258)) = A_258
      | ~ r1_tarski(A_258,B_257)
      | ~ v2_tex_2(B_257,A_256)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256)
      | ~ r1_tarski(A_258,u1_struct_0(A_256)) ) ),
    inference(resolution,[status(thm)],[c_18,c_726])).

tff(c_2059,plain,(
    ! [A_258] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_258)) = A_258
      | ~ r1_tarski(A_258,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_258,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_2050])).

tff(c_2065,plain,(
    ! [A_258] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_258)) = A_258
      | ~ r1_tarski(A_258,'#skF_5')
      | ~ r1_tarski(A_258,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_2059])).

tff(c_437,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_subset_1('#skF_2'(A_130,B_131,C_132),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ v2_tex_2(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [D_49] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',D_49) != k1_tarski('#skF_6')
      | ~ v3_pre_topc(D_49,'#skF_4')
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_445,plain,(
    ! [B_131,C_132] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_131,C_132)) != k1_tarski('#skF_6')
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_131,C_132),'#skF_4')
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_131,'#skF_4')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_437,c_32])).

tff(c_2146,plain,(
    ! [B_263,C_264] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_263,C_264)) != k1_tarski('#skF_6')
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_263,C_264),'#skF_4')
      | ~ r1_tarski(C_264,B_263)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_263,'#skF_4')
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_445])).

tff(c_2148,plain,(
    ! [A_258] :
      ( k1_tarski('#skF_6') != A_258
      | ~ v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_258),'#skF_4')
      | ~ r1_tarski(A_258,'#skF_5')
      | ~ m1_subset_1(A_258,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_258,'#skF_5')
      | ~ r1_tarski(A_258,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2065,c_2146])).

tff(c_3716,plain,(
    ! [A_401] :
      ( k1_tarski('#skF_6') != A_401
      | ~ v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_401),'#skF_4')
      | ~ m1_subset_1(A_401,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_401,'#skF_5')
      | ~ r1_tarski(A_401,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2148])).

tff(c_3743,plain,(
    ! [A_402] :
      ( k1_tarski('#skF_6') != A_402
      | ~ v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_402),'#skF_4')
      | ~ r1_tarski(A_402,'#skF_5')
      | ~ r1_tarski(A_402,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_3716])).

tff(c_3777,plain,(
    ! [A_405] :
      ( k1_tarski('#skF_6') != A_405
      | ~ r1_tarski(A_405,'#skF_5')
      | ~ r1_tarski(A_405,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1329,c_3743])).

tff(c_3817,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_983,c_3777])).

tff(c_3873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_588,c_3817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.60/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.46  
% 6.94/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.47  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_1
% 6.94/2.47  
% 6.94/2.47  %Foreground sorts:
% 6.94/2.47  
% 6.94/2.47  
% 6.94/2.47  %Background operators:
% 6.94/2.47  
% 6.94/2.47  
% 6.94/2.47  %Foreground operators:
% 6.94/2.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.94/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.94/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.94/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.94/2.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.94/2.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.94/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.94/2.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.94/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.94/2.47  tff('#skF_5', type, '#skF_5': $i).
% 6.94/2.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.94/2.47  tff('#skF_6', type, '#skF_6': $i).
% 6.94/2.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.94/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.94/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.94/2.47  tff('#skF_4', type, '#skF_4': $i).
% 6.94/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.94/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.94/2.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.94/2.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.94/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.94/2.47  
% 6.94/2.48  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tex_2)).
% 6.94/2.48  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.94/2.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.94/2.48  tff(f_40, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.94/2.48  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 6.94/2.48  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.94/2.48  tff(c_52, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.94/2.48  tff(c_56, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_52])).
% 6.94/2.48  tff(c_88, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.48  tff(c_101, plain, (![A_69]: (r1_tarski(A_69, A_69))), inference(resolution, [status(thm)], [c_88, c_4])).
% 6.94/2.48  tff(c_12, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | ~r1_tarski(k1_tarski(A_9), B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.94/2.48  tff(c_106, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(resolution, [status(thm)], [c_101, c_12])).
% 6.94/2.48  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.94/2.48  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.94/2.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.48  tff(c_94, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.48  tff(c_149, plain, (![A_79, B_80, B_81]: (r2_hidden('#skF_1'(A_79, B_80), B_81) | ~r1_tarski(A_79, B_81) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_6, c_94])).
% 6.94/2.48  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.48  tff(c_183, plain, (![A_85, B_86, B_87, B_88]: (r2_hidden('#skF_1'(A_85, B_86), B_87) | ~r1_tarski(B_88, B_87) | ~r1_tarski(A_85, B_88) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_149, c_2])).
% 6.94/2.48  tff(c_279, plain, (![A_100, B_101, B_102, A_103]: (r2_hidden('#skF_1'(A_100, B_101), B_102) | ~r1_tarski(A_100, k1_tarski(A_103)) | r1_tarski(A_100, B_101) | ~r2_hidden(A_103, B_102))), inference(resolution, [status(thm)], [c_14, c_183])).
% 6.94/2.48  tff(c_505, plain, (![A_142, B_143, B_144, A_145]: (r2_hidden('#skF_1'(k1_tarski(A_142), B_143), B_144) | r1_tarski(k1_tarski(A_142), B_143) | ~r2_hidden(A_145, B_144) | ~r2_hidden(A_142, k1_tarski(A_145)))), inference(resolution, [status(thm)], [c_14, c_279])).
% 6.94/2.48  tff(c_542, plain, (![A_146, B_147]: (r2_hidden('#skF_1'(k1_tarski(A_146), B_147), '#skF_5') | r1_tarski(k1_tarski(A_146), B_147) | ~r2_hidden(A_146, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_34, c_505])).
% 6.94/2.48  tff(c_559, plain, (![A_148]: (r1_tarski(k1_tarski(A_148), '#skF_5') | ~r2_hidden(A_148, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_542, c_4])).
% 6.94/2.48  tff(c_588, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_106, c_559])).
% 6.94/2.48  tff(c_647, plain, (![B_155]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_6'), B_155)), '#skF_5') | r1_tarski(k1_tarski('#skF_6'), B_155))), inference(resolution, [status(thm)], [c_6, c_559])).
% 6.94/2.48  tff(c_694, plain, (![B_156]: (r2_hidden('#skF_1'(k1_tarski('#skF_6'), B_156), '#skF_5') | r1_tarski(k1_tarski('#skF_6'), B_156))), inference(resolution, [status(thm)], [c_647, c_12])).
% 6.94/2.48  tff(c_954, plain, (![B_175, B_176]: (r2_hidden('#skF_1'(k1_tarski('#skF_6'), B_175), B_176) | ~r1_tarski('#skF_5', B_176) | r1_tarski(k1_tarski('#skF_6'), B_175))), inference(resolution, [status(thm)], [c_694, c_2])).
% 6.94/2.48  tff(c_983, plain, (![B_176]: (~r1_tarski('#skF_5', B_176) | r1_tarski(k1_tarski('#skF_6'), B_176))), inference(resolution, [status(thm)], [c_954, c_4])).
% 6.94/2.48  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.94/2.48  tff(c_38, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.94/2.48  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.94/2.48  tff(c_340, plain, (![A_111, B_112, C_113]: (v3_pre_topc('#skF_2'(A_111, B_112, C_113), A_111) | ~r1_tarski(C_113, B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_111))) | ~v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.94/2.48  tff(c_1314, plain, (![A_198, B_199, A_200]: (v3_pre_topc('#skF_2'(A_198, B_199, A_200), A_198) | ~r1_tarski(A_200, B_199) | ~v2_tex_2(B_199, A_198) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198) | ~r1_tarski(A_200, u1_struct_0(A_198)))), inference(resolution, [status(thm)], [c_18, c_340])).
% 6.94/2.48  tff(c_1323, plain, (![A_200]: (v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_200), '#skF_4') | ~r1_tarski(A_200, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_200, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_40, c_1314])).
% 6.94/2.48  tff(c_1329, plain, (![A_200]: (v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_200), '#skF_4') | ~r1_tarski(A_200, '#skF_5') | ~r1_tarski(A_200, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_1323])).
% 6.94/2.48  tff(c_726, plain, (![A_158, B_159, C_160]: (k9_subset_1(u1_struct_0(A_158), B_159, '#skF_2'(A_158, B_159, C_160))=C_160 | ~r1_tarski(C_160, B_159) | ~m1_subset_1(C_160, k1_zfmisc_1(u1_struct_0(A_158))) | ~v2_tex_2(B_159, A_158) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.94/2.48  tff(c_2050, plain, (![A_256, B_257, A_258]: (k9_subset_1(u1_struct_0(A_256), B_257, '#skF_2'(A_256, B_257, A_258))=A_258 | ~r1_tarski(A_258, B_257) | ~v2_tex_2(B_257, A_256) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256) | ~r1_tarski(A_258, u1_struct_0(A_256)))), inference(resolution, [status(thm)], [c_18, c_726])).
% 6.94/2.48  tff(c_2059, plain, (![A_258]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_258))=A_258 | ~r1_tarski(A_258, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_258, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_40, c_2050])).
% 6.94/2.48  tff(c_2065, plain, (![A_258]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_258))=A_258 | ~r1_tarski(A_258, '#skF_5') | ~r1_tarski(A_258, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_2059])).
% 6.94/2.48  tff(c_437, plain, (![A_130, B_131, C_132]: (m1_subset_1('#skF_2'(A_130, B_131, C_132), k1_zfmisc_1(u1_struct_0(A_130))) | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_130))) | ~v2_tex_2(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.94/2.48  tff(c_32, plain, (![D_49]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', D_49)!=k1_tarski('#skF_6') | ~v3_pre_topc(D_49, '#skF_4') | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.94/2.48  tff(c_445, plain, (![B_131, C_132]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_131, C_132))!=k1_tarski('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_4', B_131, C_132), '#skF_4') | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_131, '#skF_4') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_437, c_32])).
% 6.94/2.48  tff(c_2146, plain, (![B_263, C_264]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_263, C_264))!=k1_tarski('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_4', B_263, C_264), '#skF_4') | ~r1_tarski(C_264, B_263) | ~m1_subset_1(C_264, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_263, '#skF_4') | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_445])).
% 6.94/2.48  tff(c_2148, plain, (![A_258]: (k1_tarski('#skF_6')!=A_258 | ~v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_258), '#skF_4') | ~r1_tarski(A_258, '#skF_5') | ~m1_subset_1(A_258, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_258, '#skF_5') | ~r1_tarski(A_258, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2065, c_2146])).
% 6.94/2.48  tff(c_3716, plain, (![A_401]: (k1_tarski('#skF_6')!=A_401 | ~v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_401), '#skF_4') | ~m1_subset_1(A_401, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_401, '#skF_5') | ~r1_tarski(A_401, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2148])).
% 6.94/2.48  tff(c_3743, plain, (![A_402]: (k1_tarski('#skF_6')!=A_402 | ~v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_402), '#skF_4') | ~r1_tarski(A_402, '#skF_5') | ~r1_tarski(A_402, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_18, c_3716])).
% 6.94/2.48  tff(c_3777, plain, (![A_405]: (k1_tarski('#skF_6')!=A_405 | ~r1_tarski(A_405, '#skF_5') | ~r1_tarski(A_405, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1329, c_3743])).
% 6.94/2.48  tff(c_3817, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_983, c_3777])).
% 6.94/2.48  tff(c_3873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_588, c_3817])).
% 6.94/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.48  
% 6.94/2.48  Inference rules
% 6.94/2.48  ----------------------
% 6.94/2.48  #Ref     : 0
% 6.94/2.48  #Sup     : 960
% 6.94/2.48  #Fact    : 0
% 6.94/2.48  #Define  : 0
% 6.94/2.48  #Split   : 7
% 6.94/2.48  #Chain   : 0
% 6.94/2.48  #Close   : 0
% 6.94/2.48  
% 6.94/2.48  Ordering : KBO
% 6.94/2.48  
% 6.94/2.48  Simplification rules
% 6.94/2.48  ----------------------
% 6.94/2.48  #Subsume      : 374
% 6.94/2.48  #Demod        : 193
% 6.94/2.48  #Tautology    : 73
% 6.94/2.48  #SimpNegUnit  : 0
% 6.94/2.48  #BackRed      : 0
% 6.94/2.48  
% 6.94/2.48  #Partial instantiations: 0
% 6.94/2.48  #Strategies tried      : 1
% 6.94/2.48  
% 6.94/2.48  Timing (in seconds)
% 6.94/2.48  ----------------------
% 6.94/2.49  Preprocessing        : 0.30
% 6.94/2.49  Parsing              : 0.15
% 6.94/2.49  CNF conversion       : 0.02
% 6.94/2.49  Main loop            : 1.41
% 6.94/2.49  Inferencing          : 0.40
% 6.94/2.49  Reduction            : 0.35
% 6.94/2.49  Demodulation         : 0.23
% 6.94/2.49  BG Simplification    : 0.04
% 6.94/2.49  Subsumption          : 0.53
% 6.94/2.49  Abstraction          : 0.05
% 6.94/2.49  MUC search           : 0.00
% 6.94/2.49  Cooper               : 0.00
% 6.94/2.49  Total                : 1.75
% 6.94/2.49  Index Insertion      : 0.00
% 6.94/2.49  Index Deletion       : 0.00
% 6.94/2.49  Index Matching       : 0.00
% 6.94/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
