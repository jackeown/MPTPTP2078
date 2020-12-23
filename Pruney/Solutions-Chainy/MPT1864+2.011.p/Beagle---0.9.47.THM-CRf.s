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
% DateTime   : Thu Dec  3 10:29:15 EST 2020

% Result     : Theorem 6.82s
% Output     : CNFRefutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 126 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 375 expanded)
%              Number of equality atoms :   22 (  62 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
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
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_70,axiom,(
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

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(k1_tarski(A_9),B_10) = k1_tarski(A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_92])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_132,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_135,plain,(
    ! [B_75] : k9_subset_1(u1_struct_0('#skF_3'),B_75,'#skF_4') = k3_xboole_0(B_75,'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_132])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k9_subset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_451,plain,(
    ! [A_115,B_116,C_117] :
      ( v3_pre_topc('#skF_1'(A_115,B_116,C_117),A_115)
      | ~ r1_tarski(C_117,B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v2_tex_2(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3464,plain,(
    ! [A_337,B_338,B_339,C_340] :
      ( v3_pre_topc('#skF_1'(A_337,B_338,k9_subset_1(u1_struct_0(A_337),B_339,C_340)),A_337)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_337),B_339,C_340),B_338)
      | ~ v2_tex_2(B_338,A_337)
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ l1_pre_topc(A_337)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(u1_struct_0(A_337))) ) ),
    inference(resolution,[status(thm)],[c_14,c_451])).

tff(c_3497,plain,(
    ! [B_338,B_75] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_338,k3_xboole_0(B_75,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_75,'#skF_4'),B_338)
      | ~ v2_tex_2(B_338,'#skF_3')
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_3464])).

tff(c_3519,plain,(
    ! [B_338,B_75] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_338,k3_xboole_0(B_75,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_75,'#skF_4'),B_338)
      | ~ v2_tex_2(B_338,'#skF_3')
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_135,c_3497])).

tff(c_147,plain,(
    ! [A_78,B_79,C_80] :
      ( m1_subset_1(k9_subset_1(A_78,B_79,C_80),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_156,plain,(
    ! [B_75] :
      ( m1_subset_1(k3_xboole_0(B_75,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_147])).

tff(c_160,plain,(
    ! [B_75] : m1_subset_1(k3_xboole_0(B_75,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_156])).

tff(c_828,plain,(
    ! [A_166,B_167,C_168] :
      ( k9_subset_1(u1_struct_0(A_166),B_167,'#skF_1'(A_166,B_167,C_168)) = C_168
      | ~ r1_tarski(C_168,B_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v2_tex_2(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3845,plain,(
    ! [A_389,B_390,B_391,C_392] :
      ( k9_subset_1(u1_struct_0(A_389),B_390,'#skF_1'(A_389,B_390,k9_subset_1(u1_struct_0(A_389),B_391,C_392))) = k9_subset_1(u1_struct_0(A_389),B_391,C_392)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_389),B_391,C_392),B_390)
      | ~ v2_tex_2(B_390,A_389)
      | ~ m1_subset_1(B_390,k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ l1_pre_topc(A_389)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(u1_struct_0(A_389))) ) ),
    inference(resolution,[status(thm)],[c_14,c_828])).

tff(c_3914,plain,(
    ! [B_390,B_75] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_390,'#skF_1'('#skF_3',B_390,k3_xboole_0(B_75,'#skF_4'))) = k9_subset_1(u1_struct_0('#skF_3'),B_75,'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_75,'#skF_4'),B_390)
      | ~ v2_tex_2(B_390,'#skF_3')
      | ~ m1_subset_1(B_390,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_3845])).

tff(c_4664,plain,(
    ! [B_484,B_485] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_484,'#skF_1'('#skF_3',B_484,k3_xboole_0(B_485,'#skF_4'))) = k3_xboole_0(B_485,'#skF_4')
      | ~ r1_tarski(k3_xboole_0(B_485,'#skF_4'),B_484)
      | ~ v2_tex_2(B_484,'#skF_3')
      | ~ m1_subset_1(B_484,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_135,c_135,c_3914])).

tff(c_791,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_subset_1('#skF_1'(A_150,B_151,C_152),k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ r1_tarski(C_152,B_151)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ v2_tex_2(B_151,A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    ! [D_55] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_55) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_55,'#skF_3')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_801,plain,(
    ! [B_151,C_152] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_151,C_152)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_151,C_152),'#skF_3')
      | ~ r1_tarski(C_152,B_151)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_151,'#skF_3')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_791,c_32])).

tff(c_807,plain,(
    ! [B_151,C_152] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_151,C_152)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_151,C_152),'#skF_3')
      | ~ r1_tarski(C_152,B_151)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_151,'#skF_3')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_801])).

tff(c_4679,plain,(
    ! [B_485] :
      ( k3_xboole_0(B_485,'#skF_4') != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_485,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_485,'#skF_4'),'#skF_4')
      | ~ m1_subset_1(k3_xboole_0(B_485,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_485,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4664,c_807])).

tff(c_4718,plain,(
    ! [B_486] :
      ( k3_xboole_0(B_486,'#skF_4') != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_486,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_486,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_40,c_38,c_160,c_4679])).

tff(c_4722,plain,(
    ! [B_75] :
      ( k3_xboole_0(B_75,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_75,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_3519,c_4718])).

tff(c_4730,plain,(
    ! [B_487] :
      ( k3_xboole_0(B_487,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_487,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4722])).

tff(c_4735,plain,(
    ! [A_488] :
      ( k3_xboole_0(k1_tarski(A_488),'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_488),'#skF_4')
      | ~ r2_hidden(A_488,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4730])).

tff(c_4755,plain,(
    ! [A_491] :
      ( k3_xboole_0(k1_tarski(A_491),'#skF_4') != k1_tarski('#skF_5')
      | ~ r2_hidden(A_491,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_4735])).

tff(c_4760,plain,(
    ! [A_492] :
      ( k1_tarski(A_492) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_492,'#skF_4')
      | ~ r2_hidden(A_492,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4755])).

tff(c_4762,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_4760])).

tff(c_4766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:48:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.82/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/2.38  
% 6.82/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/2.38  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 6.82/2.38  
% 6.82/2.38  %Foreground sorts:
% 6.82/2.38  
% 6.82/2.38  
% 6.82/2.38  %Background operators:
% 6.82/2.38  
% 6.82/2.38  
% 6.82/2.38  %Foreground operators:
% 6.82/2.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.82/2.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.82/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.82/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.82/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.82/2.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.82/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.82/2.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.82/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.82/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.82/2.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.82/2.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.82/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.82/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.82/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.82/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.82/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.82/2.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.82/2.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.82/2.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.82/2.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.82/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.82/2.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.82/2.38  
% 6.82/2.39  tff(f_92, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 6.82/2.39  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.82/2.39  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.82/2.39  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.82/2.39  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 6.82/2.39  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 6.82/2.39  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.82/2.39  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.82/2.39  tff(c_92, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.82/2.39  tff(c_96, plain, (![A_9, B_10]: (k3_xboole_0(k1_tarski(A_9), B_10)=k1_tarski(A_9) | ~r2_hidden(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_92])).
% 6.82/2.39  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.82/2.39  tff(c_38, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.82/2.39  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.82/2.39  tff(c_132, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.82/2.39  tff(c_135, plain, (![B_75]: (k9_subset_1(u1_struct_0('#skF_3'), B_75, '#skF_4')=k3_xboole_0(B_75, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_132])).
% 6.82/2.39  tff(c_14, plain, (![A_11, B_12, C_13]: (m1_subset_1(k9_subset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.82/2.39  tff(c_451, plain, (![A_115, B_116, C_117]: (v3_pre_topc('#skF_1'(A_115, B_116, C_117), A_115) | ~r1_tarski(C_117, B_116) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_115))) | ~v2_tex_2(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.82/2.39  tff(c_3464, plain, (![A_337, B_338, B_339, C_340]: (v3_pre_topc('#skF_1'(A_337, B_338, k9_subset_1(u1_struct_0(A_337), B_339, C_340)), A_337) | ~r1_tarski(k9_subset_1(u1_struct_0(A_337), B_339, C_340), B_338) | ~v2_tex_2(B_338, A_337) | ~m1_subset_1(B_338, k1_zfmisc_1(u1_struct_0(A_337))) | ~l1_pre_topc(A_337) | ~m1_subset_1(C_340, k1_zfmisc_1(u1_struct_0(A_337))))), inference(resolution, [status(thm)], [c_14, c_451])).
% 6.82/2.39  tff(c_3497, plain, (![B_338, B_75]: (v3_pre_topc('#skF_1'('#skF_3', B_338, k3_xboole_0(B_75, '#skF_4')), '#skF_3') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_75, '#skF_4'), B_338) | ~v2_tex_2(B_338, '#skF_3') | ~m1_subset_1(B_338, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_135, c_3464])).
% 6.82/2.39  tff(c_3519, plain, (![B_338, B_75]: (v3_pre_topc('#skF_1'('#skF_3', B_338, k3_xboole_0(B_75, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_75, '#skF_4'), B_338) | ~v2_tex_2(B_338, '#skF_3') | ~m1_subset_1(B_338, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_135, c_3497])).
% 6.82/2.39  tff(c_147, plain, (![A_78, B_79, C_80]: (m1_subset_1(k9_subset_1(A_78, B_79, C_80), k1_zfmisc_1(A_78)) | ~m1_subset_1(C_80, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.82/2.39  tff(c_156, plain, (![B_75]: (m1_subset_1(k3_xboole_0(B_75, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_135, c_147])).
% 6.82/2.39  tff(c_160, plain, (![B_75]: (m1_subset_1(k3_xboole_0(B_75, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_156])).
% 6.82/2.39  tff(c_828, plain, (![A_166, B_167, C_168]: (k9_subset_1(u1_struct_0(A_166), B_167, '#skF_1'(A_166, B_167, C_168))=C_168 | ~r1_tarski(C_168, B_167) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_166))) | ~v2_tex_2(B_167, A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.82/2.39  tff(c_3845, plain, (![A_389, B_390, B_391, C_392]: (k9_subset_1(u1_struct_0(A_389), B_390, '#skF_1'(A_389, B_390, k9_subset_1(u1_struct_0(A_389), B_391, C_392)))=k9_subset_1(u1_struct_0(A_389), B_391, C_392) | ~r1_tarski(k9_subset_1(u1_struct_0(A_389), B_391, C_392), B_390) | ~v2_tex_2(B_390, A_389) | ~m1_subset_1(B_390, k1_zfmisc_1(u1_struct_0(A_389))) | ~l1_pre_topc(A_389) | ~m1_subset_1(C_392, k1_zfmisc_1(u1_struct_0(A_389))))), inference(resolution, [status(thm)], [c_14, c_828])).
% 6.82/2.39  tff(c_3914, plain, (![B_390, B_75]: (k9_subset_1(u1_struct_0('#skF_3'), B_390, '#skF_1'('#skF_3', B_390, k3_xboole_0(B_75, '#skF_4')))=k9_subset_1(u1_struct_0('#skF_3'), B_75, '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_75, '#skF_4'), B_390) | ~v2_tex_2(B_390, '#skF_3') | ~m1_subset_1(B_390, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_135, c_3845])).
% 6.82/2.39  tff(c_4664, plain, (![B_484, B_485]: (k9_subset_1(u1_struct_0('#skF_3'), B_484, '#skF_1'('#skF_3', B_484, k3_xboole_0(B_485, '#skF_4')))=k3_xboole_0(B_485, '#skF_4') | ~r1_tarski(k3_xboole_0(B_485, '#skF_4'), B_484) | ~v2_tex_2(B_484, '#skF_3') | ~m1_subset_1(B_484, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_135, c_135, c_3914])).
% 6.82/2.39  tff(c_791, plain, (![A_150, B_151, C_152]: (m1_subset_1('#skF_1'(A_150, B_151, C_152), k1_zfmisc_1(u1_struct_0(A_150))) | ~r1_tarski(C_152, B_151) | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0(A_150))) | ~v2_tex_2(B_151, A_150) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.82/2.39  tff(c_32, plain, (![D_55]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_55)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_55, '#skF_3') | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.82/2.39  tff(c_801, plain, (![B_151, C_152]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_151, C_152))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_151, C_152), '#skF_3') | ~r1_tarski(C_152, B_151) | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_151, '#skF_3') | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_791, c_32])).
% 6.82/2.39  tff(c_807, plain, (![B_151, C_152]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_151, C_152))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_151, C_152), '#skF_3') | ~r1_tarski(C_152, B_151) | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_151, '#skF_3') | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_801])).
% 6.82/2.39  tff(c_4679, plain, (![B_485]: (k3_xboole_0(B_485, '#skF_4')!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_485, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_485, '#skF_4'), '#skF_4') | ~m1_subset_1(k3_xboole_0(B_485, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k3_xboole_0(B_485, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_4664, c_807])).
% 6.82/2.39  tff(c_4718, plain, (![B_486]: (k3_xboole_0(B_486, '#skF_4')!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_486, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_486, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_40, c_38, c_160, c_4679])).
% 6.82/2.39  tff(c_4722, plain, (![B_75]: (k3_xboole_0(B_75, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_75, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_3519, c_4718])).
% 6.82/2.39  tff(c_4730, plain, (![B_487]: (k3_xboole_0(B_487, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_487, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4722])).
% 6.82/2.39  tff(c_4735, plain, (![A_488]: (k3_xboole_0(k1_tarski(A_488), '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_488), '#skF_4') | ~r2_hidden(A_488, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4730])).
% 6.82/2.39  tff(c_4755, plain, (![A_491]: (k3_xboole_0(k1_tarski(A_491), '#skF_4')!=k1_tarski('#skF_5') | ~r2_hidden(A_491, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_4735])).
% 6.82/2.39  tff(c_4760, plain, (![A_492]: (k1_tarski(A_492)!=k1_tarski('#skF_5') | ~r2_hidden(A_492, '#skF_4') | ~r2_hidden(A_492, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4755])).
% 6.82/2.39  tff(c_4762, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_4760])).
% 6.82/2.39  tff(c_4766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_4762])).
% 6.82/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/2.39  
% 6.82/2.39  Inference rules
% 6.82/2.39  ----------------------
% 6.82/2.39  #Ref     : 0
% 6.82/2.39  #Sup     : 1145
% 6.82/2.39  #Fact    : 0
% 6.82/2.39  #Define  : 0
% 6.82/2.39  #Split   : 2
% 6.82/2.39  #Chain   : 0
% 6.82/2.39  #Close   : 0
% 6.82/2.40  
% 6.82/2.40  Ordering : KBO
% 6.82/2.40  
% 6.82/2.40  Simplification rules
% 6.82/2.40  ----------------------
% 6.82/2.40  #Subsume      : 107
% 6.82/2.40  #Demod        : 480
% 6.82/2.40  #Tautology    : 92
% 6.82/2.40  #SimpNegUnit  : 0
% 6.82/2.40  #BackRed      : 2
% 6.82/2.40  
% 6.82/2.40  #Partial instantiations: 0
% 6.82/2.40  #Strategies tried      : 1
% 6.82/2.40  
% 6.82/2.40  Timing (in seconds)
% 6.82/2.40  ----------------------
% 6.82/2.40  Preprocessing        : 0.32
% 6.82/2.40  Parsing              : 0.17
% 6.82/2.40  CNF conversion       : 0.02
% 6.82/2.40  Main loop            : 1.34
% 6.82/2.40  Inferencing          : 0.43
% 6.82/2.40  Reduction            : 0.48
% 6.82/2.40  Demodulation         : 0.36
% 6.82/2.40  BG Simplification    : 0.06
% 6.82/2.40  Subsumption          : 0.28
% 6.82/2.40  Abstraction          : 0.08
% 6.82/2.40  MUC search           : 0.00
% 6.82/2.40  Cooper               : 0.00
% 6.82/2.40  Total                : 1.69
% 6.82/2.40  Index Insertion      : 0.00
% 6.82/2.40  Index Deletion       : 0.00
% 6.82/2.40  Index Matching       : 0.00
% 6.82/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
