%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:15 EST 2020

% Result     : Theorem 8.66s
% Output     : CNFRefutation 8.69s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 100 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 272 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_83,axiom,(
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

tff(c_58,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_158,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k1_tarski(A_100),k1_zfmisc_1(B_101))
      | ~ r2_hidden(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_166,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k1_tarski(A_100),B_101)
      | ~ r2_hidden(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_158,c_40])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_126,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(A_91,B_92)
      | ~ m1_subset_1(A_91,k1_zfmisc_1(B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_134,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_126])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,(
    k3_xboole_0('#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_134,c_20])).

tff(c_143,plain,(
    ! [D_93,B_94,A_95] :
      ( r2_hidden(D_93,B_94)
      | ~ r2_hidden(D_93,k3_xboole_0(A_95,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_146,plain,(
    ! [D_93] :
      ( r2_hidden(D_93,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_93,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_143])).

tff(c_66,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1213,plain,(
    ! [A_218,B_219,C_220] :
      ( v3_pre_topc('#skF_3'(A_218,B_219,C_220),A_218)
      | ~ r1_tarski(C_220,B_219)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ v2_tex_2(B_219,A_218)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4994,plain,(
    ! [A_373,B_374,A_375] :
      ( v3_pre_topc('#skF_3'(A_373,B_374,A_375),A_373)
      | ~ r1_tarski(A_375,B_374)
      | ~ v2_tex_2(B_374,A_373)
      | ~ m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ l1_pre_topc(A_373)
      | ~ r1_tarski(A_375,u1_struct_0(A_373)) ) ),
    inference(resolution,[status(thm)],[c_42,c_1213])).

tff(c_5006,plain,(
    ! [A_375] :
      ( v3_pre_topc('#skF_3'('#skF_5','#skF_6',A_375),'#skF_5')
      | ~ r1_tarski(A_375,'#skF_6')
      | ~ v2_tex_2('#skF_6','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_375,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_64,c_4994])).

tff(c_5013,plain,(
    ! [A_375] :
      ( v3_pre_topc('#skF_3'('#skF_5','#skF_6',A_375),'#skF_5')
      | ~ r1_tarski(A_375,'#skF_6')
      | ~ r1_tarski(A_375,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_5006])).

tff(c_1619,plain,(
    ! [A_249,B_250,C_251] :
      ( k9_subset_1(u1_struct_0(A_249),B_250,'#skF_3'(A_249,B_250,C_251)) = C_251
      | ~ r1_tarski(C_251,B_250)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ v2_tex_2(B_250,A_249)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7958,plain,(
    ! [A_472,B_473,A_474] :
      ( k9_subset_1(u1_struct_0(A_472),B_473,'#skF_3'(A_472,B_473,A_474)) = A_474
      | ~ r1_tarski(A_474,B_473)
      | ~ v2_tex_2(B_473,A_472)
      | ~ m1_subset_1(B_473,k1_zfmisc_1(u1_struct_0(A_472)))
      | ~ l1_pre_topc(A_472)
      | ~ r1_tarski(A_474,u1_struct_0(A_472)) ) ),
    inference(resolution,[status(thm)],[c_42,c_1619])).

tff(c_7970,plain,(
    ! [A_474] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6','#skF_3'('#skF_5','#skF_6',A_474)) = A_474
      | ~ r1_tarski(A_474,'#skF_6')
      | ~ v2_tex_2('#skF_6','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_474,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_64,c_7958])).

tff(c_7978,plain,(
    ! [A_475] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6','#skF_3'('#skF_5','#skF_6',A_475)) = A_475
      | ~ r1_tarski(A_475,'#skF_6')
      | ~ r1_tarski(A_475,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_7970])).

tff(c_1287,plain,(
    ! [A_229,B_230,C_231] :
      ( m1_subset_1('#skF_3'(A_229,B_230,C_231),k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ r1_tarski(C_231,B_230)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ v2_tex_2(B_230,A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    ! [D_79] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',D_79) != k1_tarski('#skF_7')
      | ~ v3_pre_topc(D_79,'#skF_5')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1308,plain,(
    ! [B_230,C_231] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6','#skF_3'('#skF_5',B_230,C_231)) != k1_tarski('#skF_7')
      | ~ v3_pre_topc('#skF_3'('#skF_5',B_230,C_231),'#skF_5')
      | ~ r1_tarski(C_231,B_230)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v2_tex_2(B_230,'#skF_5')
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1287,c_56])).

tff(c_1321,plain,(
    ! [B_230,C_231] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6','#skF_3'('#skF_5',B_230,C_231)) != k1_tarski('#skF_7')
      | ~ v3_pre_topc('#skF_3'('#skF_5',B_230,C_231),'#skF_5')
      | ~ r1_tarski(C_231,B_230)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v2_tex_2(B_230,'#skF_5')
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1308])).

tff(c_7987,plain,(
    ! [A_475] :
      ( k1_tarski('#skF_7') != A_475
      | ~ v3_pre_topc('#skF_3'('#skF_5','#skF_6',A_475),'#skF_5')
      | ~ r1_tarski(A_475,'#skF_6')
      | ~ m1_subset_1(A_475,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v2_tex_2('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_475,'#skF_6')
      | ~ r1_tarski(A_475,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7978,c_1321])).

tff(c_8008,plain,(
    ! [A_476] :
      ( k1_tarski('#skF_7') != A_476
      | ~ v3_pre_topc('#skF_3'('#skF_5','#skF_6',A_476),'#skF_5')
      | ~ m1_subset_1(A_476,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_476,'#skF_6')
      | ~ r1_tarski(A_476,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_7987])).

tff(c_8040,plain,(
    ! [A_477] :
      ( k1_tarski('#skF_7') != A_477
      | ~ v3_pre_topc('#skF_3'('#skF_5','#skF_6',A_477),'#skF_5')
      | ~ r1_tarski(A_477,'#skF_6')
      | ~ r1_tarski(A_477,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_8008])).

tff(c_8320,plain,(
    ! [A_482] :
      ( k1_tarski('#skF_7') != A_482
      | ~ r1_tarski(A_482,'#skF_6')
      | ~ r1_tarski(A_482,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5013,c_8040])).

tff(c_8349,plain,(
    ! [A_483] :
      ( k1_tarski(A_483) != k1_tarski('#skF_7')
      | ~ r1_tarski(k1_tarski(A_483),'#skF_6')
      | ~ r2_hidden(A_483,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_166,c_8320])).

tff(c_8708,plain,(
    ! [D_484] :
      ( k1_tarski(D_484) != k1_tarski('#skF_7')
      | ~ r1_tarski(k1_tarski(D_484),'#skF_6')
      | ~ r2_hidden(D_484,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_146,c_8349])).

tff(c_8714,plain,(
    ! [A_485] :
      ( k1_tarski(A_485) != k1_tarski('#skF_7')
      | ~ r2_hidden(A_485,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_166,c_8708])).

tff(c_8977,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_58,c_8714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:35:16 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.66/3.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/3.20  
% 8.66/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.69/3.21  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 8.69/3.21  
% 8.69/3.21  %Foreground sorts:
% 8.69/3.21  
% 8.69/3.21  
% 8.69/3.21  %Background operators:
% 8.69/3.21  
% 8.69/3.21  
% 8.69/3.21  %Foreground operators:
% 8.69/3.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.69/3.21  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.69/3.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.69/3.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.69/3.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.69/3.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.69/3.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.69/3.21  tff('#skF_7', type, '#skF_7': $i).
% 8.69/3.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.69/3.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.69/3.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.69/3.21  tff('#skF_5', type, '#skF_5': $i).
% 8.69/3.21  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.69/3.21  tff('#skF_6', type, '#skF_6': $i).
% 8.69/3.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.69/3.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.69/3.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.69/3.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.69/3.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.69/3.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.69/3.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.69/3.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.69/3.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.69/3.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.69/3.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.69/3.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.69/3.21  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.69/3.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.69/3.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.69/3.21  
% 8.69/3.22  tff(f_105, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 8.69/3.22  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 8.69/3.22  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.69/3.22  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.69/3.22  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.69/3.22  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 8.69/3.22  tff(c_58, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.69/3.22  tff(c_158, plain, (![A_100, B_101]: (m1_subset_1(k1_tarski(A_100), k1_zfmisc_1(B_101)) | ~r2_hidden(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.69/3.22  tff(c_40, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.69/3.22  tff(c_166, plain, (![A_100, B_101]: (r1_tarski(k1_tarski(A_100), B_101) | ~r2_hidden(A_100, B_101))), inference(resolution, [status(thm)], [c_158, c_40])).
% 8.69/3.22  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.69/3.22  tff(c_126, plain, (![A_91, B_92]: (r1_tarski(A_91, B_92) | ~m1_subset_1(A_91, k1_zfmisc_1(B_92)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.69/3.22  tff(c_134, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_126])).
% 8.69/3.22  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.69/3.22  tff(c_138, plain, (k3_xboole_0('#skF_6', u1_struct_0('#skF_5'))='#skF_6'), inference(resolution, [status(thm)], [c_134, c_20])).
% 8.69/3.22  tff(c_143, plain, (![D_93, B_94, A_95]: (r2_hidden(D_93, B_94) | ~r2_hidden(D_93, k3_xboole_0(A_95, B_94)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.69/3.22  tff(c_146, plain, (![D_93]: (r2_hidden(D_93, u1_struct_0('#skF_5')) | ~r2_hidden(D_93, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_143])).
% 8.69/3.22  tff(c_66, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.69/3.22  tff(c_62, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.69/3.22  tff(c_42, plain, (![A_41, B_42]: (m1_subset_1(A_41, k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.69/3.22  tff(c_1213, plain, (![A_218, B_219, C_220]: (v3_pre_topc('#skF_3'(A_218, B_219, C_220), A_218) | ~r1_tarski(C_220, B_219) | ~m1_subset_1(C_220, k1_zfmisc_1(u1_struct_0(A_218))) | ~v2_tex_2(B_219, A_218) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.69/3.22  tff(c_4994, plain, (![A_373, B_374, A_375]: (v3_pre_topc('#skF_3'(A_373, B_374, A_375), A_373) | ~r1_tarski(A_375, B_374) | ~v2_tex_2(B_374, A_373) | ~m1_subset_1(B_374, k1_zfmisc_1(u1_struct_0(A_373))) | ~l1_pre_topc(A_373) | ~r1_tarski(A_375, u1_struct_0(A_373)))), inference(resolution, [status(thm)], [c_42, c_1213])).
% 8.69/3.22  tff(c_5006, plain, (![A_375]: (v3_pre_topc('#skF_3'('#skF_5', '#skF_6', A_375), '#skF_5') | ~r1_tarski(A_375, '#skF_6') | ~v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_375, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_64, c_4994])).
% 8.69/3.22  tff(c_5013, plain, (![A_375]: (v3_pre_topc('#skF_3'('#skF_5', '#skF_6', A_375), '#skF_5') | ~r1_tarski(A_375, '#skF_6') | ~r1_tarski(A_375, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_5006])).
% 8.69/3.22  tff(c_1619, plain, (![A_249, B_250, C_251]: (k9_subset_1(u1_struct_0(A_249), B_250, '#skF_3'(A_249, B_250, C_251))=C_251 | ~r1_tarski(C_251, B_250) | ~m1_subset_1(C_251, k1_zfmisc_1(u1_struct_0(A_249))) | ~v2_tex_2(B_250, A_249) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.69/3.22  tff(c_7958, plain, (![A_472, B_473, A_474]: (k9_subset_1(u1_struct_0(A_472), B_473, '#skF_3'(A_472, B_473, A_474))=A_474 | ~r1_tarski(A_474, B_473) | ~v2_tex_2(B_473, A_472) | ~m1_subset_1(B_473, k1_zfmisc_1(u1_struct_0(A_472))) | ~l1_pre_topc(A_472) | ~r1_tarski(A_474, u1_struct_0(A_472)))), inference(resolution, [status(thm)], [c_42, c_1619])).
% 8.69/3.22  tff(c_7970, plain, (![A_474]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', '#skF_3'('#skF_5', '#skF_6', A_474))=A_474 | ~r1_tarski(A_474, '#skF_6') | ~v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_474, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_64, c_7958])).
% 8.69/3.22  tff(c_7978, plain, (![A_475]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', '#skF_3'('#skF_5', '#skF_6', A_475))=A_475 | ~r1_tarski(A_475, '#skF_6') | ~r1_tarski(A_475, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_7970])).
% 8.69/3.22  tff(c_1287, plain, (![A_229, B_230, C_231]: (m1_subset_1('#skF_3'(A_229, B_230, C_231), k1_zfmisc_1(u1_struct_0(A_229))) | ~r1_tarski(C_231, B_230) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0(A_229))) | ~v2_tex_2(B_230, A_229) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.69/3.22  tff(c_56, plain, (![D_79]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', D_79)!=k1_tarski('#skF_7') | ~v3_pre_topc(D_79, '#skF_5') | ~m1_subset_1(D_79, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.69/3.22  tff(c_1308, plain, (![B_230, C_231]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', '#skF_3'('#skF_5', B_230, C_231))!=k1_tarski('#skF_7') | ~v3_pre_topc('#skF_3'('#skF_5', B_230, C_231), '#skF_5') | ~r1_tarski(C_231, B_230) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v2_tex_2(B_230, '#skF_5') | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1287, c_56])).
% 8.69/3.22  tff(c_1321, plain, (![B_230, C_231]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', '#skF_3'('#skF_5', B_230, C_231))!=k1_tarski('#skF_7') | ~v3_pre_topc('#skF_3'('#skF_5', B_230, C_231), '#skF_5') | ~r1_tarski(C_231, B_230) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v2_tex_2(B_230, '#skF_5') | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1308])).
% 8.69/3.22  tff(c_7987, plain, (![A_475]: (k1_tarski('#skF_7')!=A_475 | ~v3_pre_topc('#skF_3'('#skF_5', '#skF_6', A_475), '#skF_5') | ~r1_tarski(A_475, '#skF_6') | ~m1_subset_1(A_475, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_475, '#skF_6') | ~r1_tarski(A_475, u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_7978, c_1321])).
% 8.69/3.22  tff(c_8008, plain, (![A_476]: (k1_tarski('#skF_7')!=A_476 | ~v3_pre_topc('#skF_3'('#skF_5', '#skF_6', A_476), '#skF_5') | ~m1_subset_1(A_476, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_476, '#skF_6') | ~r1_tarski(A_476, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_7987])).
% 8.69/3.22  tff(c_8040, plain, (![A_477]: (k1_tarski('#skF_7')!=A_477 | ~v3_pre_topc('#skF_3'('#skF_5', '#skF_6', A_477), '#skF_5') | ~r1_tarski(A_477, '#skF_6') | ~r1_tarski(A_477, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_42, c_8008])).
% 8.69/3.22  tff(c_8320, plain, (![A_482]: (k1_tarski('#skF_7')!=A_482 | ~r1_tarski(A_482, '#skF_6') | ~r1_tarski(A_482, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_5013, c_8040])).
% 8.69/3.22  tff(c_8349, plain, (![A_483]: (k1_tarski(A_483)!=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski(A_483), '#skF_6') | ~r2_hidden(A_483, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_166, c_8320])).
% 8.69/3.22  tff(c_8708, plain, (![D_484]: (k1_tarski(D_484)!=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski(D_484), '#skF_6') | ~r2_hidden(D_484, '#skF_6'))), inference(resolution, [status(thm)], [c_146, c_8349])).
% 8.69/3.22  tff(c_8714, plain, (![A_485]: (k1_tarski(A_485)!=k1_tarski('#skF_7') | ~r2_hidden(A_485, '#skF_6'))), inference(resolution, [status(thm)], [c_166, c_8708])).
% 8.69/3.22  tff(c_8977, plain, $false, inference(resolution, [status(thm)], [c_58, c_8714])).
% 8.69/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.69/3.22  
% 8.69/3.22  Inference rules
% 8.69/3.22  ----------------------
% 8.69/3.22  #Ref     : 0
% 8.69/3.22  #Sup     : 2192
% 8.69/3.22  #Fact    : 0
% 8.69/3.22  #Define  : 0
% 8.69/3.22  #Split   : 5
% 8.69/3.22  #Chain   : 0
% 8.69/3.22  #Close   : 0
% 8.69/3.22  
% 8.69/3.22  Ordering : KBO
% 8.69/3.22  
% 8.69/3.22  Simplification rules
% 8.69/3.22  ----------------------
% 8.69/3.22  #Subsume      : 307
% 8.69/3.22  #Demod        : 569
% 8.69/3.22  #Tautology    : 95
% 8.69/3.22  #SimpNegUnit  : 1
% 8.69/3.22  #BackRed      : 6
% 8.69/3.22  
% 8.69/3.22  #Partial instantiations: 0
% 8.69/3.22  #Strategies tried      : 1
% 8.69/3.22  
% 8.69/3.22  Timing (in seconds)
% 8.69/3.22  ----------------------
% 8.69/3.22  Preprocessing        : 0.35
% 8.69/3.22  Parsing              : 0.18
% 8.69/3.22  CNF conversion       : 0.03
% 8.69/3.22  Main loop            : 2.05
% 8.69/3.22  Inferencing          : 0.56
% 8.69/3.22  Reduction            : 0.47
% 8.69/3.22  Demodulation         : 0.33
% 8.69/3.22  BG Simplification    : 0.11
% 8.69/3.22  Subsumption          : 0.74
% 8.69/3.22  Abstraction          : 0.18
% 8.69/3.22  MUC search           : 0.00
% 8.69/3.22  Cooper               : 0.00
% 8.69/3.22  Total                : 2.43
% 8.69/3.22  Index Insertion      : 0.00
% 8.69/3.22  Index Deletion       : 0.00
% 8.69/3.22  Index Matching       : 0.00
% 8.69/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
