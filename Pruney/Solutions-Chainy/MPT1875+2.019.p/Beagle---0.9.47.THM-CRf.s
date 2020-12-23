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
% DateTime   : Thu Dec  3 10:29:48 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 290 expanded)
%              Number of leaves         :   25 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 740 expanded)
%              Number of equality atoms :    5 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_connsp_2(C,A,B)
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_18,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_4,c_30])).

tff(c_39,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_24,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_45,plain,(
    ! [A_31] :
      ( v2_tex_2(u1_struct_0(A_31),A_31)
      | ~ v1_tdlat_3(A_31)
      | ~ m1_subset_1(u1_struct_0(A_31),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,
    ( v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_45])).

tff(c_53,plain,
    ( v2_tex_2(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_39,c_24,c_39,c_48])).

tff(c_54,plain,
    ( v2_tex_2(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_53])).

tff(c_58,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_20])).

tff(c_59,plain,(
    ! [A_32,B_33] :
      ( m2_connsp_2(k2_struct_0(A_32),A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    ! [B_33] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_59])).

tff(c_63,plain,(
    ! [B_33] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_61])).

tff(c_65,plain,(
    ! [B_34] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_63])).

tff(c_69,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_90,plain,(
    ! [C_39,A_40,B_41] :
      ( m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m2_connsp_2(C_39,A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_90])).

tff(c_95,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_40,c_39,c_39,c_92])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_95])).

tff(c_99,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_98,plain,(
    v2_tex_2(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_102,plain,(
    ! [A_42,B_43] :
      ( m2_connsp_2(k2_struct_0(A_42),A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104,plain,(
    ! [B_43] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_102])).

tff(c_106,plain,(
    ! [B_43] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_104])).

tff(c_108,plain,(
    ! [B_44] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_106])).

tff(c_116,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_108])).

tff(c_141,plain,(
    ! [B_49,C_50,A_51] :
      ( r1_tarski(B_49,C_50)
      | ~ m2_connsp_2(C_50,A_51,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_145,plain,
    ( r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_116,c_141])).

tff(c_152,plain,
    ( r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_40,c_39,c_145])).

tff(c_153,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_152])).

tff(c_154,plain,(
    ! [C_52,A_53,B_54] :
      ( v2_tex_2(C_52,A_53)
      | ~ v2_tex_2(B_54,A_53)
      | ~ r1_tarski(C_52,B_54)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_161,plain,(
    ! [A_55] :
      ( v2_tex_2('#skF_2',A_55)
      | ~ v2_tex_2(k2_struct_0('#skF_1'),A_55)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_153,c_154])).

tff(c_164,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_161])).

tff(c_166,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_99,c_40,c_39,c_98,c_164])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_166])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.31  %$ m2_connsp_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.02/1.31  
% 2.02/1.31  %Foreground sorts:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Background operators:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Foreground operators:
% 2.02/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.02/1.31  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.02/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.31  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.02/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.02/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.02/1.31  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.02/1.31  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.02/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.31  
% 2.29/1.33  tff(f_114, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 2.29/1.33  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.29/1.33  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.29/1.33  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 2.29/1.33  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.29/1.33  tff(f_44, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 2.29/1.33  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_connsp_2)).
% 2.29/1.33  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 2.29/1.33  tff(c_18, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.29/1.33  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.29/1.33  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.29/1.33  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.33  tff(c_30, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.33  tff(c_35, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_4, c_30])).
% 2.29/1.33  tff(c_39, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_35])).
% 2.29/1.33  tff(c_24, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.29/1.33  tff(c_45, plain, (![A_31]: (v2_tex_2(u1_struct_0(A_31), A_31) | ~v1_tdlat_3(A_31) | ~m1_subset_1(u1_struct_0(A_31), k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.29/1.33  tff(c_48, plain, (v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~v1_tdlat_3('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_39, c_45])).
% 2.29/1.33  tff(c_53, plain, (v2_tex_2(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_39, c_24, c_39, c_48])).
% 2.29/1.33  tff(c_54, plain, (v2_tex_2(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_28, c_53])).
% 2.29/1.33  tff(c_58, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_54])).
% 2.29/1.33  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.29/1.33  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.29/1.33  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_20])).
% 2.29/1.33  tff(c_59, plain, (![A_32, B_33]: (m2_connsp_2(k2_struct_0(A_32), A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.29/1.33  tff(c_61, plain, (![B_33]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_59])).
% 2.29/1.33  tff(c_63, plain, (![B_33]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_61])).
% 2.29/1.33  tff(c_65, plain, (![B_34]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_28, c_63])).
% 2.29/1.33  tff(c_69, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_65])).
% 2.29/1.33  tff(c_90, plain, (![C_39, A_40, B_41]: (m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~m2_connsp_2(C_39, A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.33  tff(c_92, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_90])).
% 2.29/1.33  tff(c_95, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_40, c_39, c_39, c_92])).
% 2.29/1.33  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_95])).
% 2.29/1.33  tff(c_99, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 2.29/1.33  tff(c_98, plain, (v2_tex_2(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 2.29/1.33  tff(c_102, plain, (![A_42, B_43]: (m2_connsp_2(k2_struct_0(A_42), A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.29/1.33  tff(c_104, plain, (![B_43]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_102])).
% 2.29/1.33  tff(c_106, plain, (![B_43]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_104])).
% 2.29/1.33  tff(c_108, plain, (![B_44]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_28, c_106])).
% 2.29/1.33  tff(c_116, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_108])).
% 2.29/1.33  tff(c_141, plain, (![B_49, C_50, A_51]: (r1_tarski(B_49, C_50) | ~m2_connsp_2(C_50, A_51, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.29/1.33  tff(c_145, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_116, c_141])).
% 2.29/1.33  tff(c_152, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_40, c_39, c_145])).
% 2.29/1.33  tff(c_153, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_28, c_152])).
% 2.29/1.33  tff(c_154, plain, (![C_52, A_53, B_54]: (v2_tex_2(C_52, A_53) | ~v2_tex_2(B_54, A_53) | ~r1_tarski(C_52, B_54) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.29/1.33  tff(c_161, plain, (![A_55]: (v2_tex_2('#skF_2', A_55) | ~v2_tex_2(k2_struct_0('#skF_1'), A_55) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_153, c_154])).
% 2.29/1.33  tff(c_164, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_39, c_161])).
% 2.29/1.33  tff(c_166, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_99, c_40, c_39, c_98, c_164])).
% 2.29/1.33  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_166])).
% 2.29/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  Inference rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Ref     : 0
% 2.29/1.33  #Sup     : 24
% 2.29/1.33  #Fact    : 0
% 2.29/1.33  #Define  : 0
% 2.29/1.33  #Split   : 1
% 2.29/1.33  #Chain   : 0
% 2.29/1.33  #Close   : 0
% 2.29/1.33  
% 2.29/1.33  Ordering : KBO
% 2.29/1.33  
% 2.29/1.33  Simplification rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Subsume      : 3
% 2.29/1.33  #Demod        : 69
% 2.29/1.33  #Tautology    : 8
% 2.29/1.33  #SimpNegUnit  : 13
% 2.29/1.33  #BackRed      : 1
% 2.29/1.33  
% 2.29/1.33  #Partial instantiations: 0
% 2.29/1.33  #Strategies tried      : 1
% 2.29/1.33  
% 2.29/1.33  Timing (in seconds)
% 2.29/1.33  ----------------------
% 2.29/1.33  Preprocessing        : 0.32
% 2.29/1.33  Parsing              : 0.18
% 2.29/1.33  CNF conversion       : 0.02
% 2.29/1.33  Main loop            : 0.16
% 2.29/1.33  Inferencing          : 0.05
% 2.29/1.33  Reduction            : 0.05
% 2.29/1.33  Demodulation         : 0.04
% 2.29/1.33  BG Simplification    : 0.01
% 2.29/1.33  Subsumption          : 0.02
% 2.29/1.33  Abstraction          : 0.01
% 2.29/1.33  MUC search           : 0.00
% 2.29/1.33  Cooper               : 0.00
% 2.29/1.33  Total                : 0.51
% 2.29/1.33  Index Insertion      : 0.00
% 2.29/1.33  Index Deletion       : 0.00
% 2.29/1.33  Index Matching       : 0.00
% 2.29/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
