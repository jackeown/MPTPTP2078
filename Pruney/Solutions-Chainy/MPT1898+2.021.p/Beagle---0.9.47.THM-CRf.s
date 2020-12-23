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
% DateTime   : Thu Dec  3 10:30:33 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 240 expanded)
%              Number of leaves         :   32 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          :  178 ( 817 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => ( C = D
                        | r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),D))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tex_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_115,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1('#skF_4'(A_71,B_72),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ v2_tex_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v3_tdlat_3(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    ! [B_42] :
      ( ~ v3_tex_2(B_42,'#skF_5')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_130,plain,(
    ! [B_72] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_72),'#skF_5')
      | ~ v2_tex_2(B_72,'#skF_5')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_115,c_34])).

tff(c_138,plain,(
    ! [B_72] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_72),'#skF_5')
      | ~ v2_tex_2(B_72,'#skF_5')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_130])).

tff(c_140,plain,(
    ! [B_73] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_73),'#skF_5')
      | ~ v2_tex_2(B_73,'#skF_5')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_138])).

tff(c_158,plain,
    ( ~ v3_tex_2('#skF_4'('#skF_5','#skF_1'(u1_struct_0('#skF_5'))),'#skF_5')
    | ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_140])).

tff(c_159,plain,(
    ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_26,plain,(
    ! [A_10,B_24] :
      ( m1_subset_1('#skF_2'(A_10,B_24),u1_struct_0(A_10))
      | v2_tex_2(B_24,A_10)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v3_tdlat_3(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [A_7,B_9] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_7),B_9),A_7)
      | ~ m1_subset_1(B_9,u1_struct_0(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k6_domain_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ! [A_53,B_54] :
      ( v3_tex_2('#skF_4'(A_53,B_54),A_53)
      | ~ v2_tex_2(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v3_tdlat_3(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_209,plain,(
    ! [A_87,B_88] :
      ( v3_tex_2('#skF_4'(A_87,k6_domain_1(u1_struct_0(A_87),B_88)),A_87)
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_87),B_88),A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v3_tdlat_3(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87)
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | v1_xboole_0(u1_struct_0(A_87)) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_157,plain,(
    ! [B_6] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_6)),'#skF_5')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'),B_6),'#skF_5')
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_10,c_140])).

tff(c_161,plain,(
    ! [B_6] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_6)),'#skF_5')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'),B_6),'#skF_5')
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_213,plain,(
    ! [B_88] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'),B_88),'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_209,c_161])).

tff(c_216,plain,(
    ! [B_88] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'),B_88),'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_213])).

tff(c_217,plain,(
    ! [B_88] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'),B_88),'#skF_5')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_216])).

tff(c_219,plain,(
    ! [B_89] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'),B_89),'#skF_5')
      | ~ m1_subset_1(B_89,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_223,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_219])).

tff(c_226,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_223])).

tff(c_228,plain,(
    ! [B_90] : ~ m1_subset_1(B_90,u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_226])).

tff(c_232,plain,(
    ! [B_24] :
      ( v2_tex_2(B_24,'#skF_5')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_239,plain,(
    ! [B_24] :
      ( v2_tex_2(B_24,'#skF_5')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_232])).

tff(c_245,plain,(
    ! [B_91] :
      ( v2_tex_2(B_91,'#skF_5')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_239])).

tff(c_257,plain,(
    v2_tex_2('#skF_1'(u1_struct_0('#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_245])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_257])).

tff(c_267,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_274,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_267,c_8])).

tff(c_277,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_274])).

tff(c_280,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_280])).

tff(c_285,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_288,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_285,c_8])).

tff(c_291,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_288])).

tff(c_294,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_291])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_294])).

tff(c_300,plain,(
    v2_tex_2('#skF_1'(u1_struct_0('#skF_5')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_70,plain,(
    ! [A_53] :
      ( v3_tex_2('#skF_4'(A_53,'#skF_1'(u1_struct_0(A_53))),A_53)
      | ~ v2_tex_2('#skF_1'(u1_struct_0(A_53)),A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v3_tdlat_3(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_62])).

tff(c_299,plain,(
    ~ v3_tex_2('#skF_4'('#skF_5','#skF_1'(u1_struct_0('#skF_5'))),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_303,plain,
    ( ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_5')),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_299])).

tff(c_306,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_300,c_303])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.37  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.53/1.37  
% 2.53/1.37  %Foreground sorts:
% 2.53/1.37  
% 2.53/1.37  
% 2.53/1.37  %Background operators:
% 2.53/1.37  
% 2.53/1.37  
% 2.53/1.37  %Foreground operators:
% 2.53/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.53/1.37  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.53/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.37  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.53/1.37  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.53/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.53/1.37  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.53/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.53/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.37  
% 2.53/1.39  tff(f_127, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.53/1.39  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.53/1.39  tff(f_30, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.53/1.39  tff(f_112, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.53/1.39  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r2_hidden(D, B)) => ((C = D) | r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tex_2)).
% 2.53/1.39  tff(f_61, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.53/1.39  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.53/1.39  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.53/1.39  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.39  tff(c_40, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.39  tff(c_38, plain, (v3_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.39  tff(c_36, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.39  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.39  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.53/1.39  tff(c_115, plain, (![A_71, B_72]: (m1_subset_1('#skF_4'(A_71, B_72), k1_zfmisc_1(u1_struct_0(A_71))) | ~v2_tex_2(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v3_tdlat_3(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.53/1.39  tff(c_34, plain, (![B_42]: (~v3_tex_2(B_42, '#skF_5') | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.39  tff(c_130, plain, (![B_72]: (~v3_tex_2('#skF_4'('#skF_5', B_72), '#skF_5') | ~v2_tex_2(B_72, '#skF_5') | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_115, c_34])).
% 2.53/1.39  tff(c_138, plain, (![B_72]: (~v3_tex_2('#skF_4'('#skF_5', B_72), '#skF_5') | ~v2_tex_2(B_72, '#skF_5') | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_130])).
% 2.53/1.39  tff(c_140, plain, (![B_73]: (~v3_tex_2('#skF_4'('#skF_5', B_73), '#skF_5') | ~v2_tex_2(B_73, '#skF_5') | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_138])).
% 2.53/1.39  tff(c_158, plain, (~v3_tex_2('#skF_4'('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))), '#skF_5') | ~v2_tex_2('#skF_1'(u1_struct_0('#skF_5')), '#skF_5')), inference(resolution, [status(thm)], [c_4, c_140])).
% 2.53/1.39  tff(c_159, plain, (~v2_tex_2('#skF_1'(u1_struct_0('#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_158])).
% 2.53/1.39  tff(c_26, plain, (![A_10, B_24]: (m1_subset_1('#skF_2'(A_10, B_24), u1_struct_0(A_10)) | v2_tex_2(B_24, A_10) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10) | ~v3_tdlat_3(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.53/1.39  tff(c_12, plain, (![A_7, B_9]: (v2_tex_2(k6_domain_1(u1_struct_0(A_7), B_9), A_7) | ~m1_subset_1(B_9, u1_struct_0(A_7)) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.39  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k6_domain_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.39  tff(c_62, plain, (![A_53, B_54]: (v3_tex_2('#skF_4'(A_53, B_54), A_53) | ~v2_tex_2(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v3_tdlat_3(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.53/1.39  tff(c_209, plain, (![A_87, B_88]: (v3_tex_2('#skF_4'(A_87, k6_domain_1(u1_struct_0(A_87), B_88)), A_87) | ~v2_tex_2(k6_domain_1(u1_struct_0(A_87), B_88), A_87) | ~l1_pre_topc(A_87) | ~v3_tdlat_3(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | v1_xboole_0(u1_struct_0(A_87)))), inference(resolution, [status(thm)], [c_10, c_62])).
% 2.53/1.39  tff(c_157, plain, (![B_6]: (~v3_tex_2('#skF_4'('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_6)), '#skF_5') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'), B_6), '#skF_5') | ~m1_subset_1(B_6, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_10, c_140])).
% 2.53/1.39  tff(c_161, plain, (![B_6]: (~v3_tex_2('#skF_4'('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_6)), '#skF_5') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'), B_6), '#skF_5') | ~m1_subset_1(B_6, u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_157])).
% 2.53/1.39  tff(c_213, plain, (![B_88]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'), B_88), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(B_88, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_209, c_161])).
% 2.53/1.39  tff(c_216, plain, (![B_88]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'), B_88), '#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(B_88, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_213])).
% 2.53/1.39  tff(c_217, plain, (![B_88]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'), B_88), '#skF_5') | ~m1_subset_1(B_88, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_42, c_216])).
% 2.53/1.39  tff(c_219, plain, (![B_89]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'), B_89), '#skF_5') | ~m1_subset_1(B_89, u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_217])).
% 2.53/1.39  tff(c_223, plain, (![B_9]: (~m1_subset_1(B_9, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_219])).
% 2.53/1.39  tff(c_226, plain, (![B_9]: (~m1_subset_1(B_9, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_223])).
% 2.53/1.39  tff(c_228, plain, (![B_90]: (~m1_subset_1(B_90, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_42, c_226])).
% 2.53/1.39  tff(c_232, plain, (![B_24]: (v2_tex_2(B_24, '#skF_5') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_228])).
% 2.53/1.39  tff(c_239, plain, (![B_24]: (v2_tex_2(B_24, '#skF_5') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_232])).
% 2.53/1.39  tff(c_245, plain, (![B_91]: (v2_tex_2(B_91, '#skF_5') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_239])).
% 2.53/1.39  tff(c_257, plain, (v2_tex_2('#skF_1'(u1_struct_0('#skF_5')), '#skF_5')), inference(resolution, [status(thm)], [c_4, c_245])).
% 2.53/1.39  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_257])).
% 2.53/1.39  tff(c_267, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_217])).
% 2.53/1.39  tff(c_8, plain, (![A_4]: (~v1_xboole_0(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.39  tff(c_274, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_267, c_8])).
% 2.53/1.39  tff(c_277, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_274])).
% 2.53/1.39  tff(c_280, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_277])).
% 2.53/1.39  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_280])).
% 2.53/1.39  tff(c_285, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_157])).
% 2.53/1.39  tff(c_288, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_285, c_8])).
% 2.53/1.39  tff(c_291, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_288])).
% 2.53/1.39  tff(c_294, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_291])).
% 2.53/1.39  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_294])).
% 2.53/1.39  tff(c_300, plain, (v2_tex_2('#skF_1'(u1_struct_0('#skF_5')), '#skF_5')), inference(splitRight, [status(thm)], [c_158])).
% 2.53/1.39  tff(c_70, plain, (![A_53]: (v3_tex_2('#skF_4'(A_53, '#skF_1'(u1_struct_0(A_53))), A_53) | ~v2_tex_2('#skF_1'(u1_struct_0(A_53)), A_53) | ~l1_pre_topc(A_53) | ~v3_tdlat_3(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_4, c_62])).
% 2.53/1.39  tff(c_299, plain, (~v3_tex_2('#skF_4'('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))), '#skF_5')), inference(splitRight, [status(thm)], [c_158])).
% 2.53/1.39  tff(c_303, plain, (~v2_tex_2('#skF_1'(u1_struct_0('#skF_5')), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_299])).
% 2.53/1.39  tff(c_306, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_300, c_303])).
% 2.53/1.39  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_306])).
% 2.53/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.39  
% 2.53/1.39  Inference rules
% 2.53/1.39  ----------------------
% 2.53/1.39  #Ref     : 0
% 2.53/1.39  #Sup     : 41
% 2.53/1.39  #Fact    : 0
% 2.53/1.39  #Define  : 0
% 2.53/1.39  #Split   : 5
% 2.53/1.39  #Chain   : 0
% 2.53/1.39  #Close   : 0
% 2.53/1.39  
% 2.53/1.39  Ordering : KBO
% 2.53/1.39  
% 2.53/1.39  Simplification rules
% 2.53/1.39  ----------------------
% 2.53/1.39  #Subsume      : 11
% 2.53/1.39  #Demod        : 35
% 2.53/1.39  #Tautology    : 0
% 2.53/1.39  #SimpNegUnit  : 14
% 2.53/1.39  #BackRed      : 0
% 2.53/1.39  
% 2.53/1.39  #Partial instantiations: 0
% 2.53/1.39  #Strategies tried      : 1
% 2.53/1.39  
% 2.53/1.39  Timing (in seconds)
% 2.53/1.39  ----------------------
% 2.53/1.39  Preprocessing        : 0.31
% 2.53/1.39  Parsing              : 0.16
% 2.53/1.39  CNF conversion       : 0.02
% 2.53/1.39  Main loop            : 0.24
% 2.53/1.39  Inferencing          : 0.10
% 2.53/1.39  Reduction            : 0.06
% 2.53/1.39  Demodulation         : 0.04
% 2.53/1.39  BG Simplification    : 0.02
% 2.53/1.39  Subsumption          : 0.04
% 2.53/1.39  Abstraction          : 0.02
% 2.53/1.39  MUC search           : 0.00
% 2.53/1.39  Cooper               : 0.00
% 2.53/1.39  Total                : 0.59
% 2.53/1.39  Index Insertion      : 0.00
% 2.53/1.39  Index Deletion       : 0.00
% 2.53/1.39  Index Matching       : 0.00
% 2.53/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
