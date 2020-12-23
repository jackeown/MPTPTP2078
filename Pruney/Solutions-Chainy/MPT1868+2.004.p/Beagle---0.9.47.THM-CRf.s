%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:35 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 161 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 465 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & v2_pre_topc(B) )
           => ( ~ v2_struct_0(B)
              & v1_tdlat_3(B)
              & v2_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_131,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_51,plain,(
    ! [A_35,B_36] :
      ( ~ v2_struct_0(k1_tex_2(A_35,B_36))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_57,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54])).

tff(c_58,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_57])).

tff(c_67,plain,(
    ! [A_39,B_40] :
      ( m1_pre_topc(k1_tex_2(A_39,B_40),A_39)
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_69,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_72,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_69])).

tff(c_73,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_72])).

tff(c_43,plain,(
    ! [A_33,B_34] :
      ( v7_struct_0(k1_tex_2(A_33,B_34))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_49,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46])).

tff(c_50,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_49])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,
    ( v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_79,plain,(
    v2_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_76])).

tff(c_90,plain,(
    ! [B_43,A_44] :
      ( v1_tdlat_3(B_43)
      | ~ v2_pre_topc(B_43)
      | ~ v7_struct_0(B_43)
      | v2_struct_0(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_93,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_90])).

tff(c_96,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_50,c_79,c_93])).

tff(c_97,plain,(
    v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_58,c_96])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( m1_subset_1(u1_struct_0(B_6),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [B_45,A_46] :
      ( v2_tex_2(u1_struct_0(B_45),A_46)
      | ~ v1_tdlat_3(B_45)
      | ~ m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_pre_topc(B_45,A_46)
      | v2_struct_0(B_45)
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_102,plain,(
    ! [B_6,A_4] :
      ( v2_tex_2(u1_struct_0(B_6),A_4)
      | ~ v1_tdlat_3(B_6)
      | v2_struct_0(B_6)
      | v2_struct_0(A_4)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_59,plain,(
    ! [A_37,B_38] :
      ( v1_pre_topc(k1_tex_2(A_37,B_38))
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_65,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62])).

tff(c_66,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_65])).

tff(c_115,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(u1_struct_0(A_56),B_57) = u1_struct_0(k1_tex_2(A_56,B_57))
      | ~ m1_pre_topc(k1_tex_2(A_56,B_57),A_56)
      | ~ v1_pre_topc(k1_tex_2(A_56,B_57))
      | v2_struct_0(k1_tex_2(A_56,B_57))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_117,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_115])).

tff(c_120,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_66,c_117])).

tff(c_121,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_58,c_120])).

tff(c_32,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_122,plain,(
    ~ v2_tex_2(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_32])).

tff(c_134,plain,
    ( ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_122])).

tff(c_137,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_73,c_97,c_134])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_58,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.28  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.24/1.28  
% 2.24/1.28  %Foreground sorts:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Background operators:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Foreground operators:
% 2.24/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.28  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.24/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.28  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.24/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.24/1.28  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.24/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.28  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.24/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.28  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.24/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.24/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.28  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.24/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.28  
% 2.24/1.30  tff(f_144, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.24/1.30  tff(f_111, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.24/1.30  tff(f_97, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.24/1.30  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.24/1.30  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & v7_struct_0(B)) & v2_pre_topc(B)) => ((~v2_struct_0(B) & v1_tdlat_3(B)) & v2_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc25_tex_2)).
% 2.24/1.30  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.24/1.30  tff(f_131, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.24/1.30  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 2.24/1.30  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.24/1.30  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.24/1.30  tff(c_34, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.24/1.30  tff(c_51, plain, (![A_35, B_36]: (~v2_struct_0(k1_tex_2(A_35, B_36)) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~l1_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.30  tff(c_54, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_51])).
% 2.24/1.30  tff(c_57, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54])).
% 2.24/1.30  tff(c_58, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_57])).
% 2.24/1.30  tff(c_67, plain, (![A_39, B_40]: (m1_pre_topc(k1_tex_2(A_39, B_40), A_39) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.24/1.30  tff(c_69, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_67])).
% 2.24/1.30  tff(c_72, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_69])).
% 2.24/1.30  tff(c_73, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_72])).
% 2.24/1.30  tff(c_43, plain, (![A_33, B_34]: (v7_struct_0(k1_tex_2(A_33, B_34)) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.30  tff(c_46, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_43])).
% 2.24/1.30  tff(c_49, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46])).
% 2.24/1.30  tff(c_50, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_49])).
% 2.24/1.30  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.24/1.30  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.30  tff(c_76, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_2])).
% 2.24/1.30  tff(c_79, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_76])).
% 2.24/1.30  tff(c_90, plain, (![B_43, A_44]: (v1_tdlat_3(B_43) | ~v2_pre_topc(B_43) | ~v7_struct_0(B_43) | v2_struct_0(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.30  tff(c_93, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_73, c_90])).
% 2.24/1.30  tff(c_96, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_50, c_79, c_93])).
% 2.24/1.30  tff(c_97, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_58, c_96])).
% 2.24/1.30  tff(c_4, plain, (![B_6, A_4]: (m1_subset_1(u1_struct_0(B_6), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.30  tff(c_98, plain, (![B_45, A_46]: (v2_tex_2(u1_struct_0(B_45), A_46) | ~v1_tdlat_3(B_45) | ~m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_pre_topc(B_45, A_46) | v2_struct_0(B_45) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.24/1.30  tff(c_102, plain, (![B_6, A_4]: (v2_tex_2(u1_struct_0(B_6), A_4) | ~v1_tdlat_3(B_6) | v2_struct_0(B_6) | v2_struct_0(A_4) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_4, c_98])).
% 2.24/1.30  tff(c_59, plain, (![A_37, B_38]: (v1_pre_topc(k1_tex_2(A_37, B_38)) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.30  tff(c_62, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_59])).
% 2.24/1.30  tff(c_65, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62])).
% 2.24/1.30  tff(c_66, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_65])).
% 2.24/1.30  tff(c_115, plain, (![A_56, B_57]: (k6_domain_1(u1_struct_0(A_56), B_57)=u1_struct_0(k1_tex_2(A_56, B_57)) | ~m1_pre_topc(k1_tex_2(A_56, B_57), A_56) | ~v1_pre_topc(k1_tex_2(A_56, B_57)) | v2_struct_0(k1_tex_2(A_56, B_57)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.24/1.30  tff(c_117, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_73, c_115])).
% 2.24/1.30  tff(c_120, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_66, c_117])).
% 2.24/1.30  tff(c_121, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_58, c_120])).
% 2.24/1.30  tff(c_32, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.24/1.30  tff(c_122, plain, (~v2_tex_2(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_32])).
% 2.24/1.30  tff(c_134, plain, (~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_102, c_122])).
% 2.24/1.30  tff(c_137, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_73, c_97, c_134])).
% 2.24/1.30  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_58, c_137])).
% 2.24/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  Inference rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Ref     : 0
% 2.24/1.30  #Sup     : 15
% 2.24/1.30  #Fact    : 0
% 2.24/1.30  #Define  : 0
% 2.24/1.30  #Split   : 0
% 2.24/1.30  #Chain   : 0
% 2.24/1.30  #Close   : 0
% 2.24/1.30  
% 2.24/1.30  Ordering : KBO
% 2.24/1.30  
% 2.24/1.30  Simplification rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Subsume      : 4
% 2.24/1.30  #Demod        : 21
% 2.24/1.30  #Tautology    : 4
% 2.24/1.30  #SimpNegUnit  : 9
% 2.24/1.30  #BackRed      : 1
% 2.24/1.30  
% 2.24/1.30  #Partial instantiations: 0
% 2.24/1.30  #Strategies tried      : 1
% 2.24/1.30  
% 2.24/1.30  Timing (in seconds)
% 2.24/1.30  ----------------------
% 2.24/1.30  Preprocessing        : 0.33
% 2.24/1.30  Parsing              : 0.18
% 2.24/1.30  CNF conversion       : 0.02
% 2.24/1.30  Main loop            : 0.15
% 2.24/1.30  Inferencing          : 0.06
% 2.24/1.30  Reduction            : 0.05
% 2.24/1.30  Demodulation         : 0.03
% 2.24/1.30  BG Simplification    : 0.01
% 2.24/1.30  Subsumption          : 0.03
% 2.24/1.30  Abstraction          : 0.01
% 2.24/1.30  MUC search           : 0.00
% 2.24/1.30  Cooper               : 0.00
% 2.24/1.30  Total                : 0.51
% 2.24/1.30  Index Insertion      : 0.00
% 2.24/1.30  Index Deletion       : 0.00
% 2.24/1.30  Index Matching       : 0.00
% 2.24/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
