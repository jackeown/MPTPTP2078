%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:32 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 148 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 481 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_20,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_24,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_7),B_9),A_7)
      | ~ m1_subset_1(B_9,u1_struct_0(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k6_domain_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [A_27,B_28] :
      ( v3_tex_2('#skF_2'(A_27,B_28),A_27)
      | ~ v2_tex_2(B_28,A_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v3_tdlat_3(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_112,plain,(
    ! [A_40,B_41] :
      ( v3_tex_2('#skF_2'(A_40,k6_domain_1(u1_struct_0(A_40),B_41)),A_40)
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_40),B_41),A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v3_tdlat_3(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40)
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | v1_xboole_0(u1_struct_0(A_40)) ) ),
    inference(resolution,[status(thm)],[c_8,c_45])).

tff(c_63,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1('#skF_2'(A_31,B_32),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ v2_tex_2(B_32,A_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v3_tdlat_3(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [B_17] :
      ( ~ v3_tex_2(B_17,'#skF_3')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_71,plain,(
    ! [B_32] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_32),'#skF_3')
      | ~ v2_tex_2(B_32,'#skF_3')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_63,c_18])).

tff(c_76,plain,(
    ! [B_32] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_32),'#skF_3')
      | ~ v2_tex_2(B_32,'#skF_3')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_71])).

tff(c_78,plain,(
    ! [B_33] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_33),'#skF_3')
      | ~ v2_tex_2(B_33,'#skF_3')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_76])).

tff(c_95,plain,(
    ! [B_6] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_6)),'#skF_3')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_6),'#skF_3')
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_99,plain,(
    ! [B_6] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_6)),'#skF_3')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_6),'#skF_3')
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_116,plain,(
    ! [B_41] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_41),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_112,c_99])).

tff(c_119,plain,(
    ! [B_41] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_41),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_116])).

tff(c_120,plain,(
    ! [B_41] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_41),'#skF_3')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_119])).

tff(c_141,plain,(
    ! [B_43] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_43),'#skF_3')
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_145,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_148,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_145])).

tff(c_150,plain,(
    ! [B_44] : ~ m1_subset_1(B_44,u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_148])).

tff(c_155,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_156,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_159,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_156,c_6])).

tff(c_162,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_159])).

tff(c_165,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_165])).

tff(c_170,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_173,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_6])).

tff(c_176,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_173])).

tff(c_179,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.21  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2
% 2.07/1.21  
% 2.07/1.21  %Foreground sorts:
% 2.07/1.21  
% 2.07/1.21  
% 2.07/1.21  %Background operators:
% 2.07/1.21  
% 2.07/1.21  
% 2.07/1.21  %Foreground operators:
% 2.07/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.07/1.21  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.07/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.21  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.07/1.21  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.07/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.07/1.21  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.07/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.07/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.21  
% 2.07/1.23  tff(f_97, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.07/1.23  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.07/1.23  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.07/1.23  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.07/1.23  tff(f_47, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.07/1.23  tff(f_82, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.07/1.23  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.07/1.23  tff(c_20, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.07/1.23  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.23  tff(c_26, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.07/1.23  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.07/1.23  tff(c_24, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.07/1.23  tff(c_10, plain, (![A_7, B_9]: (v2_tex_2(k6_domain_1(u1_struct_0(A_7), B_9), A_7) | ~m1_subset_1(B_9, u1_struct_0(A_7)) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.23  tff(c_22, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.07/1.23  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k6_domain_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.23  tff(c_45, plain, (![A_27, B_28]: (v3_tex_2('#skF_2'(A_27, B_28), A_27) | ~v2_tex_2(B_28, A_27) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v3_tdlat_3(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.23  tff(c_112, plain, (![A_40, B_41]: (v3_tex_2('#skF_2'(A_40, k6_domain_1(u1_struct_0(A_40), B_41)), A_40) | ~v2_tex_2(k6_domain_1(u1_struct_0(A_40), B_41), A_40) | ~l1_pre_topc(A_40) | ~v3_tdlat_3(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | v1_xboole_0(u1_struct_0(A_40)))), inference(resolution, [status(thm)], [c_8, c_45])).
% 2.07/1.23  tff(c_63, plain, (![A_31, B_32]: (m1_subset_1('#skF_2'(A_31, B_32), k1_zfmisc_1(u1_struct_0(A_31))) | ~v2_tex_2(B_32, A_31) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v3_tdlat_3(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.23  tff(c_18, plain, (![B_17]: (~v3_tex_2(B_17, '#skF_3') | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.07/1.23  tff(c_71, plain, (![B_32]: (~v3_tex_2('#skF_2'('#skF_3', B_32), '#skF_3') | ~v2_tex_2(B_32, '#skF_3') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_63, c_18])).
% 2.07/1.23  tff(c_76, plain, (![B_32]: (~v3_tex_2('#skF_2'('#skF_3', B_32), '#skF_3') | ~v2_tex_2(B_32, '#skF_3') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_71])).
% 2.07/1.23  tff(c_78, plain, (![B_33]: (~v3_tex_2('#skF_2'('#skF_3', B_33), '#skF_3') | ~v2_tex_2(B_33, '#skF_3') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_26, c_76])).
% 2.07/1.23  tff(c_95, plain, (![B_6]: (~v3_tex_2('#skF_2'('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_6)), '#skF_3') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_6), '#skF_3') | ~m1_subset_1(B_6, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_78])).
% 2.07/1.23  tff(c_99, plain, (![B_6]: (~v3_tex_2('#skF_2'('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_6)), '#skF_3') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_6), '#skF_3') | ~m1_subset_1(B_6, u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_95])).
% 2.07/1.23  tff(c_116, plain, (![B_41]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_41), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_41, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_112, c_99])).
% 2.07/1.23  tff(c_119, plain, (![B_41]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_41), '#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_41, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_116])).
% 2.07/1.23  tff(c_120, plain, (![B_41]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_41), '#skF_3') | ~m1_subset_1(B_41, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_26, c_119])).
% 2.07/1.23  tff(c_141, plain, (![B_43]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_43), '#skF_3') | ~m1_subset_1(B_43, u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_120])).
% 2.07/1.23  tff(c_145, plain, (![B_9]: (~m1_subset_1(B_9, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_141])).
% 2.07/1.23  tff(c_148, plain, (![B_9]: (~m1_subset_1(B_9, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_145])).
% 2.07/1.23  tff(c_150, plain, (![B_44]: (~m1_subset_1(B_44, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_26, c_148])).
% 2.07/1.23  tff(c_155, plain, $false, inference(resolution, [status(thm)], [c_2, c_150])).
% 2.07/1.23  tff(c_156, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_120])).
% 2.07/1.23  tff(c_6, plain, (![A_4]: (~v1_xboole_0(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.07/1.23  tff(c_159, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_156, c_6])).
% 2.07/1.23  tff(c_162, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_159])).
% 2.07/1.23  tff(c_165, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_162])).
% 2.07/1.23  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_165])).
% 2.07/1.23  tff(c_170, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_95])).
% 2.07/1.23  tff(c_173, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_170, c_6])).
% 2.07/1.23  tff(c_176, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_173])).
% 2.07/1.23  tff(c_179, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_176])).
% 2.07/1.23  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_179])).
% 2.07/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  Inference rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Ref     : 0
% 2.07/1.23  #Sup     : 23
% 2.07/1.23  #Fact    : 0
% 2.07/1.23  #Define  : 0
% 2.07/1.23  #Split   : 4
% 2.07/1.23  #Chain   : 0
% 2.07/1.23  #Close   : 0
% 2.07/1.23  
% 2.07/1.23  Ordering : KBO
% 2.07/1.23  
% 2.07/1.23  Simplification rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Subsume      : 6
% 2.07/1.23  #Demod        : 19
% 2.07/1.23  #Tautology    : 0
% 2.07/1.23  #SimpNegUnit  : 8
% 2.07/1.23  #BackRed      : 0
% 2.07/1.23  
% 2.07/1.23  #Partial instantiations: 0
% 2.07/1.23  #Strategies tried      : 1
% 2.07/1.23  
% 2.07/1.23  Timing (in seconds)
% 2.07/1.23  ----------------------
% 2.07/1.23  Preprocessing        : 0.28
% 2.07/1.23  Parsing              : 0.16
% 2.07/1.23  CNF conversion       : 0.02
% 2.07/1.23  Main loop            : 0.18
% 2.07/1.23  Inferencing          : 0.08
% 2.07/1.23  Reduction            : 0.05
% 2.07/1.23  Demodulation         : 0.03
% 2.07/1.23  BG Simplification    : 0.01
% 2.07/1.23  Subsumption          : 0.03
% 2.07/1.23  Abstraction          : 0.01
% 2.07/1.23  MUC search           : 0.00
% 2.07/1.23  Cooper               : 0.00
% 2.07/1.23  Total                : 0.49
% 2.07/1.23  Index Insertion      : 0.00
% 2.07/1.23  Index Deletion       : 0.00
% 2.07/1.23  Index Matching       : 0.00
% 2.07/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
