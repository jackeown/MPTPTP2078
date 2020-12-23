%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:35 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 162 expanded)
%              Number of leaves         :   27 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 461 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & ~ v1_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tex_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_59,plain,(
    ! [A_39,B_40] :
      ( ~ v2_struct_0(k1_tex_2(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_59])).

tff(c_65,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_62])).

tff(c_66,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_65])).

tff(c_75,plain,(
    ! [A_43,B_44] :
      ( m1_pre_topc(k1_tex_2(A_43,B_44),A_43)
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_77,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_80,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_77])).

tff(c_81,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_80])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( l1_pre_topc(B_6)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_93,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_87])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84,plain,
    ( v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_90,plain,(
    v2_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_84])).

tff(c_47,plain,(
    ! [A_37,B_38] :
      ( v7_struct_0(k1_tex_2(A_37,B_38))
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_53,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50])).

tff(c_54,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_53])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v7_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_10])).

tff(c_95,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_90,c_58])).

tff(c_96,plain,(
    v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_95])).

tff(c_6,plain,(
    ! [B_9,A_7] :
      ( m1_subset_1(u1_struct_0(B_9),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    ! [B_45,A_46] :
      ( v2_tex_2(u1_struct_0(B_45),A_46)
      | ~ v1_tdlat_3(B_45)
      | ~ m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_pre_topc(B_45,A_46)
      | v2_struct_0(B_45)
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_101,plain,(
    ! [B_9,A_7] :
      ( v2_tex_2(u1_struct_0(B_9),A_7)
      | ~ v1_tdlat_3(B_9)
      | v2_struct_0(B_9)
      | v2_struct_0(A_7)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_67,plain,(
    ! [A_41,B_42] :
      ( v1_pre_topc(k1_tex_2(A_41,B_42))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_67])).

tff(c_73,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_70])).

tff(c_74,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_73])).

tff(c_114,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(u1_struct_0(A_56),B_57) = u1_struct_0(k1_tex_2(A_56,B_57))
      | ~ m1_pre_topc(k1_tex_2(A_56,B_57),A_56)
      | ~ v1_pre_topc(k1_tex_2(A_56,B_57))
      | v2_struct_0(k1_tex_2(A_56,B_57))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_116,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_114])).

tff(c_119,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_74,c_116])).

tff(c_120,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_66,c_119])).

tff(c_34,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_121,plain,(
    ~ v2_tex_2(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_34])).

tff(c_133,plain,
    ( ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_121])).

tff(c_136,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_81,c_96,c_133])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_66,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:53:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.22  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.06/1.22  
% 2.06/1.22  %Foreground sorts:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Background operators:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Foreground operators:
% 2.06/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.22  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.06/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.06/1.22  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.06/1.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.06/1.22  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.06/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.22  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.06/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.22  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.06/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.06/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.06/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.22  
% 2.18/1.24  tff(f_147, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.18/1.24  tff(f_114, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.18/1.24  tff(f_100, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.18/1.24  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.18/1.24  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.18/1.24  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v2_pre_topc(A)) & ~v1_tdlat_3(A)) => ((~v2_struct_0(A) & ~v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_tex_1)).
% 2.18/1.24  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.18/1.24  tff(f_134, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 2.18/1.24  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 2.18/1.24  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.18/1.24  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.18/1.24  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.18/1.24  tff(c_59, plain, (![A_39, B_40]: (~v2_struct_0(k1_tex_2(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.18/1.24  tff(c_62, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_59])).
% 2.18/1.24  tff(c_65, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_62])).
% 2.18/1.24  tff(c_66, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_65])).
% 2.18/1.24  tff(c_75, plain, (![A_43, B_44]: (m1_pre_topc(k1_tex_2(A_43, B_44), A_43) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.24  tff(c_77, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_75])).
% 2.18/1.24  tff(c_80, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_77])).
% 2.18/1.24  tff(c_81, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_80])).
% 2.18/1.24  tff(c_4, plain, (![B_6, A_4]: (l1_pre_topc(B_6) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.24  tff(c_87, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_81, c_4])).
% 2.18/1.24  tff(c_93, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_87])).
% 2.18/1.24  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.18/1.24  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.24  tff(c_84, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.18/1.24  tff(c_90, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_84])).
% 2.18/1.24  tff(c_47, plain, (![A_37, B_38]: (v7_struct_0(k1_tex_2(A_37, B_38)) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.18/1.24  tff(c_50, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_47])).
% 2.18/1.24  tff(c_53, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50])).
% 2.18/1.24  tff(c_54, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_53])).
% 2.18/1.24  tff(c_10, plain, (![A_10]: (~v7_struct_0(A_10) | v1_tdlat_3(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.18/1.24  tff(c_58, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_10])).
% 2.18/1.24  tff(c_95, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_90, c_58])).
% 2.18/1.24  tff(c_96, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_95])).
% 2.18/1.24  tff(c_6, plain, (![B_9, A_7]: (m1_subset_1(u1_struct_0(B_9), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.18/1.24  tff(c_97, plain, (![B_45, A_46]: (v2_tex_2(u1_struct_0(B_45), A_46) | ~v1_tdlat_3(B_45) | ~m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_pre_topc(B_45, A_46) | v2_struct_0(B_45) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.18/1.24  tff(c_101, plain, (![B_9, A_7]: (v2_tex_2(u1_struct_0(B_9), A_7) | ~v1_tdlat_3(B_9) | v2_struct_0(B_9) | v2_struct_0(A_7) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_6, c_97])).
% 2.18/1.24  tff(c_67, plain, (![A_41, B_42]: (v1_pre_topc(k1_tex_2(A_41, B_42)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.18/1.24  tff(c_70, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_67])).
% 2.18/1.24  tff(c_73, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_70])).
% 2.18/1.24  tff(c_74, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_73])).
% 2.18/1.24  tff(c_114, plain, (![A_56, B_57]: (k6_domain_1(u1_struct_0(A_56), B_57)=u1_struct_0(k1_tex_2(A_56, B_57)) | ~m1_pre_topc(k1_tex_2(A_56, B_57), A_56) | ~v1_pre_topc(k1_tex_2(A_56, B_57)) | v2_struct_0(k1_tex_2(A_56, B_57)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.18/1.24  tff(c_116, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_81, c_114])).
% 2.18/1.24  tff(c_119, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_74, c_116])).
% 2.18/1.24  tff(c_120, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_66, c_119])).
% 2.18/1.24  tff(c_34, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.18/1.24  tff(c_121, plain, (~v2_tex_2(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_34])).
% 2.18/1.24  tff(c_133, plain, (~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_121])).
% 2.18/1.24  tff(c_136, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_81, c_96, c_133])).
% 2.18/1.24  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_66, c_136])).
% 2.18/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  Inference rules
% 2.18/1.24  ----------------------
% 2.18/1.24  #Ref     : 0
% 2.18/1.24  #Sup     : 15
% 2.18/1.24  #Fact    : 0
% 2.18/1.24  #Define  : 0
% 2.18/1.24  #Split   : 0
% 2.18/1.24  #Chain   : 0
% 2.18/1.24  #Close   : 0
% 2.18/1.24  
% 2.18/1.24  Ordering : KBO
% 2.18/1.24  
% 2.18/1.24  Simplification rules
% 2.18/1.24  ----------------------
% 2.18/1.24  #Subsume      : 4
% 2.18/1.24  #Demod        : 18
% 2.18/1.24  #Tautology    : 5
% 2.18/1.24  #SimpNegUnit  : 8
% 2.18/1.24  #BackRed      : 1
% 2.18/1.24  
% 2.18/1.24  #Partial instantiations: 0
% 2.18/1.24  #Strategies tried      : 1
% 2.18/1.24  
% 2.18/1.24  Timing (in seconds)
% 2.18/1.24  ----------------------
% 2.21/1.24  Preprocessing        : 0.32
% 2.21/1.24  Parsing              : 0.17
% 2.21/1.24  CNF conversion       : 0.02
% 2.21/1.24  Main loop            : 0.15
% 2.21/1.24  Inferencing          : 0.06
% 2.21/1.24  Reduction            : 0.05
% 2.21/1.24  Demodulation         : 0.03
% 2.21/1.24  BG Simplification    : 0.01
% 2.21/1.24  Subsumption          : 0.03
% 2.21/1.24  Abstraction          : 0.01
% 2.21/1.24  MUC search           : 0.00
% 2.21/1.24  Cooper               : 0.00
% 2.21/1.24  Total                : 0.51
% 2.21/1.24  Index Insertion      : 0.00
% 2.21/1.24  Index Deletion       : 0.00
% 2.21/1.24  Index Matching       : 0.00
% 2.21/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
