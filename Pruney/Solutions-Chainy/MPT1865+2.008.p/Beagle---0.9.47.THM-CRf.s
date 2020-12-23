%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:18 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 119 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 326 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_94,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_94,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(A_89,B_90)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_94])).

tff(c_124,plain,(
    ! [A_96,C_97,B_98] :
      ( r1_tarski(A_96,C_97)
      | ~ r1_tarski(B_98,C_97)
      | ~ r1_tarski(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [A_96] :
      ( r1_tarski(A_96,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_96,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_103,c_124])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_744,plain,(
    ! [A_173,B_174,C_175] :
      ( v4_pre_topc('#skF_2'(A_173,B_174,C_175),A_173)
      | ~ r1_tarski(C_175,B_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ v2_tex_2(B_174,A_173)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1820,plain,(
    ! [A_244,B_245,A_246] :
      ( v4_pre_topc('#skF_2'(A_244,B_245,A_246),A_244)
      | ~ r1_tarski(A_246,B_245)
      | ~ v2_tex_2(B_245,A_244)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_pre_topc(A_244)
      | ~ r1_tarski(A_246,u1_struct_0(A_244)) ) ),
    inference(resolution,[status(thm)],[c_26,c_744])).

tff(c_1843,plain,(
    ! [A_244,A_38,A_246] :
      ( v4_pre_topc('#skF_2'(A_244,A_38,A_246),A_244)
      | ~ r1_tarski(A_246,A_38)
      | ~ v2_tex_2(A_38,A_244)
      | ~ l1_pre_topc(A_244)
      | ~ r1_tarski(A_246,u1_struct_0(A_244))
      | ~ r1_tarski(A_38,u1_struct_0(A_244)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1820])).

tff(c_1484,plain,(
    ! [A_227,B_228,C_229] :
      ( k9_subset_1(u1_struct_0(A_227),B_228,'#skF_2'(A_227,B_228,C_229)) = C_229
      | ~ r1_tarski(C_229,B_228)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ v2_tex_2(B_228,A_227)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3941,plain,(
    ! [A_327,B_328,A_329] :
      ( k9_subset_1(u1_struct_0(A_327),B_328,'#skF_2'(A_327,B_328,A_329)) = A_329
      | ~ r1_tarski(A_329,B_328)
      | ~ v2_tex_2(B_328,A_327)
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ l1_pre_topc(A_327)
      | ~ r1_tarski(A_329,u1_struct_0(A_327)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1484])).

tff(c_3959,plain,(
    ! [A_329] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_329)) = A_329
      | ~ r1_tarski(A_329,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_329,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_52,c_3941])).

tff(c_3968,plain,(
    ! [A_329] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_329)) = A_329
      | ~ r1_tarski(A_329,'#skF_5')
      | ~ r1_tarski(A_329,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_3959])).

tff(c_1260,plain,(
    ! [A_211,B_212,C_213] :
      ( m1_subset_1('#skF_2'(A_211,B_212,C_213),k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ r1_tarski(C_213,B_212)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ v2_tex_2(B_212,A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    ! [D_80] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',D_80) != k1_tarski('#skF_6')
      | ~ v4_pre_topc(D_80,'#skF_4')
      | ~ m1_subset_1(D_80,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1282,plain,(
    ! [B_212,C_213] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_212,C_213)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4',B_212,C_213),'#skF_4')
      | ~ r1_tarski(C_213,B_212)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_212,'#skF_4')
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1260,c_44])).

tff(c_4973,plain,(
    ! [B_369,C_370] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_369,C_370)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4',B_369,C_370),'#skF_4')
      | ~ r1_tarski(C_370,B_369)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_369,'#skF_4')
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1282])).

tff(c_4975,plain,(
    ! [A_329] :
      ( k1_tarski('#skF_6') != A_329
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_329),'#skF_4')
      | ~ r1_tarski(A_329,'#skF_5')
      | ~ m1_subset_1(A_329,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_329,'#skF_5')
      | ~ r1_tarski(A_329,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3968,c_4973])).

tff(c_4984,plain,(
    ! [A_371] :
      ( k1_tarski('#skF_6') != A_371
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_371),'#skF_4')
      | ~ m1_subset_1(A_371,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_371,'#skF_5')
      | ~ r1_tarski(A_371,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4975])).

tff(c_5029,plain,(
    ! [A_372] :
      ( k1_tarski('#skF_6') != A_372
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',A_372),'#skF_4')
      | ~ r1_tarski(A_372,'#skF_5')
      | ~ r1_tarski(A_372,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_26,c_4984])).

tff(c_5041,plain,(
    ! [A_246] :
      ( k1_tarski('#skF_6') != A_246
      | ~ r1_tarski(A_246,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_246,u1_struct_0('#skF_4'))
      | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1843,c_5029])).

tff(c_5063,plain,(
    ! [A_373] :
      ( k1_tarski('#skF_6') != A_373
      | ~ r1_tarski(A_373,'#skF_5')
      | ~ r1_tarski(A_373,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54,c_50,c_5041])).

tff(c_5286,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_130,c_5063])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    ! [B_82,A_83] :
      ( ~ r2_hidden(B_82,A_83)
      | ~ v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_79,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(A_86,B_87)
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_87,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_79])).

tff(c_145,plain,(
    ! [A_103,B_104] :
      ( k6_domain_1(A_103,B_104) = k1_tarski(B_104)
      | ~ m1_subset_1(B_104,A_103)
      | v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_154,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_87,c_145])).

tff(c_165,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_154])).

tff(c_203,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1(k6_domain_1(A_112,B_113),k1_zfmisc_1(A_112))
      | ~ m1_subset_1(B_113,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_219,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_203])).

tff(c_225,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_219])).

tff(c_226,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_225])).

tff(c_24,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_234,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_226,c_24])).

tff(c_5288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5286,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.25/2.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/2.58  
% 7.25/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/2.58  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.25/2.58  
% 7.25/2.58  %Foreground sorts:
% 7.25/2.58  
% 7.25/2.58  
% 7.25/2.58  %Background operators:
% 7.25/2.58  
% 7.25/2.58  
% 7.25/2.58  %Foreground operators:
% 7.25/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.25/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.25/2.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.25/2.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.25/2.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.25/2.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.25/2.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.25/2.58  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.25/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.25/2.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.25/2.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.25/2.58  tff('#skF_5', type, '#skF_5': $i).
% 7.25/2.58  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.25/2.58  tff('#skF_6', type, '#skF_6': $i).
% 7.25/2.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.25/2.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.25/2.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.25/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.25/2.58  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.25/2.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.25/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.25/2.58  tff('#skF_4', type, '#skF_4': $i).
% 7.25/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.25/2.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.25/2.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.25/2.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.25/2.58  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.25/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.25/2.58  
% 7.45/2.60  tff(f_116, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 7.45/2.60  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.45/2.60  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.45/2.60  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 7.45/2.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.45/2.60  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.45/2.60  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.45/2.60  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 7.45/2.60  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.45/2.60  tff(c_94, plain, (![A_89, B_90]: (r1_tarski(A_89, B_90) | ~m1_subset_1(A_89, k1_zfmisc_1(B_90)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.45/2.60  tff(c_103, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_94])).
% 7.45/2.60  tff(c_124, plain, (![A_96, C_97, B_98]: (r1_tarski(A_96, C_97) | ~r1_tarski(B_98, C_97) | ~r1_tarski(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.45/2.60  tff(c_130, plain, (![A_96]: (r1_tarski(A_96, u1_struct_0('#skF_4')) | ~r1_tarski(A_96, '#skF_5'))), inference(resolution, [status(thm)], [c_103, c_124])).
% 7.45/2.60  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.45/2.60  tff(c_50, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.45/2.60  tff(c_26, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.45/2.60  tff(c_744, plain, (![A_173, B_174, C_175]: (v4_pre_topc('#skF_2'(A_173, B_174, C_175), A_173) | ~r1_tarski(C_175, B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(u1_struct_0(A_173))) | ~v2_tex_2(B_174, A_173) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.45/2.60  tff(c_1820, plain, (![A_244, B_245, A_246]: (v4_pre_topc('#skF_2'(A_244, B_245, A_246), A_244) | ~r1_tarski(A_246, B_245) | ~v2_tex_2(B_245, A_244) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))) | ~l1_pre_topc(A_244) | ~r1_tarski(A_246, u1_struct_0(A_244)))), inference(resolution, [status(thm)], [c_26, c_744])).
% 7.45/2.60  tff(c_1843, plain, (![A_244, A_38, A_246]: (v4_pre_topc('#skF_2'(A_244, A_38, A_246), A_244) | ~r1_tarski(A_246, A_38) | ~v2_tex_2(A_38, A_244) | ~l1_pre_topc(A_244) | ~r1_tarski(A_246, u1_struct_0(A_244)) | ~r1_tarski(A_38, u1_struct_0(A_244)))), inference(resolution, [status(thm)], [c_26, c_1820])).
% 7.45/2.60  tff(c_1484, plain, (![A_227, B_228, C_229]: (k9_subset_1(u1_struct_0(A_227), B_228, '#skF_2'(A_227, B_228, C_229))=C_229 | ~r1_tarski(C_229, B_228) | ~m1_subset_1(C_229, k1_zfmisc_1(u1_struct_0(A_227))) | ~v2_tex_2(B_228, A_227) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.45/2.60  tff(c_3941, plain, (![A_327, B_328, A_329]: (k9_subset_1(u1_struct_0(A_327), B_328, '#skF_2'(A_327, B_328, A_329))=A_329 | ~r1_tarski(A_329, B_328) | ~v2_tex_2(B_328, A_327) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0(A_327))) | ~l1_pre_topc(A_327) | ~r1_tarski(A_329, u1_struct_0(A_327)))), inference(resolution, [status(thm)], [c_26, c_1484])).
% 7.45/2.60  tff(c_3959, plain, (![A_329]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_329))=A_329 | ~r1_tarski(A_329, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_329, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_52, c_3941])).
% 7.45/2.60  tff(c_3968, plain, (![A_329]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_329))=A_329 | ~r1_tarski(A_329, '#skF_5') | ~r1_tarski(A_329, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_3959])).
% 7.45/2.60  tff(c_1260, plain, (![A_211, B_212, C_213]: (m1_subset_1('#skF_2'(A_211, B_212, C_213), k1_zfmisc_1(u1_struct_0(A_211))) | ~r1_tarski(C_213, B_212) | ~m1_subset_1(C_213, k1_zfmisc_1(u1_struct_0(A_211))) | ~v2_tex_2(B_212, A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_211))) | ~l1_pre_topc(A_211))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.45/2.60  tff(c_44, plain, (![D_80]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', D_80)!=k1_tarski('#skF_6') | ~v4_pre_topc(D_80, '#skF_4') | ~m1_subset_1(D_80, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.45/2.60  tff(c_1282, plain, (![B_212, C_213]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_212, C_213))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', B_212, C_213), '#skF_4') | ~r1_tarski(C_213, B_212) | ~m1_subset_1(C_213, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_212, '#skF_4') | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1260, c_44])).
% 7.45/2.60  tff(c_4973, plain, (![B_369, C_370]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_369, C_370))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', B_369, C_370), '#skF_4') | ~r1_tarski(C_370, B_369) | ~m1_subset_1(C_370, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_369, '#skF_4') | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1282])).
% 7.45/2.60  tff(c_4975, plain, (![A_329]: (k1_tarski('#skF_6')!=A_329 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_329), '#skF_4') | ~r1_tarski(A_329, '#skF_5') | ~m1_subset_1(A_329, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_329, '#skF_5') | ~r1_tarski(A_329, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3968, c_4973])).
% 7.45/2.60  tff(c_4984, plain, (![A_371]: (k1_tarski('#skF_6')!=A_371 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_371), '#skF_4') | ~m1_subset_1(A_371, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_371, '#skF_5') | ~r1_tarski(A_371, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4975])).
% 7.45/2.60  tff(c_5029, plain, (![A_372]: (k1_tarski('#skF_6')!=A_372 | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', A_372), '#skF_4') | ~r1_tarski(A_372, '#skF_5') | ~r1_tarski(A_372, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_26, c_4984])).
% 7.45/2.60  tff(c_5041, plain, (![A_246]: (k1_tarski('#skF_6')!=A_246 | ~r1_tarski(A_246, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_246, u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1843, c_5029])).
% 7.45/2.60  tff(c_5063, plain, (![A_373]: (k1_tarski('#skF_6')!=A_373 | ~r1_tarski(A_373, '#skF_5') | ~r1_tarski(A_373, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_54, c_50, c_5041])).
% 7.45/2.60  tff(c_5286, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_130, c_5063])).
% 7.45/2.60  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.45/2.60  tff(c_64, plain, (![B_82, A_83]: (~r2_hidden(B_82, A_83) | ~v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.45/2.60  tff(c_68, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_64])).
% 7.45/2.60  tff(c_79, plain, (![A_86, B_87]: (m1_subset_1(A_86, B_87) | ~r2_hidden(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.45/2.60  tff(c_87, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_79])).
% 7.45/2.60  tff(c_145, plain, (![A_103, B_104]: (k6_domain_1(A_103, B_104)=k1_tarski(B_104) | ~m1_subset_1(B_104, A_103) | v1_xboole_0(A_103))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.45/2.60  tff(c_154, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_87, c_145])).
% 7.45/2.60  tff(c_165, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_154])).
% 7.45/2.60  tff(c_203, plain, (![A_112, B_113]: (m1_subset_1(k6_domain_1(A_112, B_113), k1_zfmisc_1(A_112)) | ~m1_subset_1(B_113, A_112) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.45/2.60  tff(c_219, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_165, c_203])).
% 7.45/2.60  tff(c_225, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_219])).
% 7.45/2.60  tff(c_226, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_225])).
% 7.45/2.60  tff(c_24, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.45/2.60  tff(c_234, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_226, c_24])).
% 7.45/2.60  tff(c_5288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5286, c_234])).
% 7.45/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.60  
% 7.45/2.60  Inference rules
% 7.45/2.60  ----------------------
% 7.45/2.60  #Ref     : 0
% 7.45/2.60  #Sup     : 1180
% 7.45/2.60  #Fact    : 0
% 7.45/2.60  #Define  : 0
% 7.45/2.60  #Split   : 7
% 7.45/2.60  #Chain   : 0
% 7.45/2.60  #Close   : 0
% 7.45/2.60  
% 7.45/2.60  Ordering : KBO
% 7.45/2.60  
% 7.45/2.60  Simplification rules
% 7.45/2.60  ----------------------
% 7.45/2.60  #Subsume      : 70
% 7.45/2.60  #Demod        : 211
% 7.45/2.60  #Tautology    : 135
% 7.45/2.60  #SimpNegUnit  : 25
% 7.45/2.60  #BackRed      : 1
% 7.45/2.60  
% 7.45/2.60  #Partial instantiations: 0
% 7.45/2.60  #Strategies tried      : 1
% 7.45/2.60  
% 7.45/2.60  Timing (in seconds)
% 7.45/2.60  ----------------------
% 7.45/2.61  Preprocessing        : 0.33
% 7.45/2.61  Parsing              : 0.18
% 7.45/2.61  CNF conversion       : 0.02
% 7.45/2.61  Main loop            : 1.50
% 7.45/2.61  Inferencing          : 0.46
% 7.45/2.61  Reduction            : 0.39
% 7.45/2.61  Demodulation         : 0.27
% 7.45/2.61  BG Simplification    : 0.06
% 7.45/2.61  Subsumption          : 0.49
% 7.45/2.61  Abstraction          : 0.08
% 7.45/2.61  MUC search           : 0.00
% 7.45/2.61  Cooper               : 0.00
% 7.45/2.61  Total                : 1.87
% 7.45/2.61  Index Insertion      : 0.00
% 7.45/2.61  Index Deletion       : 0.00
% 7.45/2.61  Index Matching       : 0.00
% 7.45/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
