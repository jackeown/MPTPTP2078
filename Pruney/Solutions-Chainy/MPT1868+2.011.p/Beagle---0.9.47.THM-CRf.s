%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:36 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 129 expanded)
%              Number of leaves         :   25 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 361 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v2_pre_topc(k1_tex_2(A,B))
           => ( v1_tdlat_3(k1_tex_2(A,B))
              & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_109,axiom,(
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

tff(f_61,axiom,(
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

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_43,plain,(
    ! [A_33,B_34] :
      ( ~ v2_struct_0(k1_tex_2(A_33,B_34))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_43])).

tff(c_49,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_46])).

tff(c_50,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_49])).

tff(c_51,plain,(
    ! [A_35,B_36] :
      ( m1_pre_topc(k1_tex_2(A_35,B_36),A_35)
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_53,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_51])).

tff(c_56,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_53])).

tff(c_57,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_56])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,
    ( v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_63,plain,(
    v2_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_60])).

tff(c_72,plain,(
    ! [A_39,B_40] :
      ( v1_tdlat_3(k1_tex_2(A_39,B_40))
      | ~ v2_pre_topc(k1_tex_2(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_75,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_78,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_63,c_75])).

tff(c_79,plain,(
    v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_78])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( m1_subset_1(u1_struct_0(B_6),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [B_41,A_42] :
      ( v2_tex_2(u1_struct_0(B_41),A_42)
      | ~ v1_tdlat_3(B_41)
      | ~ m1_subset_1(u1_struct_0(B_41),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_pre_topc(B_41,A_42)
      | v2_struct_0(B_41)
      | ~ l1_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_84,plain,(
    ! [B_6,A_4] :
      ( v2_tex_2(u1_struct_0(B_6),A_4)
      | ~ v1_tdlat_3(B_6)
      | v2_struct_0(B_6)
      | v2_struct_0(A_4)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_80])).

tff(c_35,plain,(
    ! [A_31,B_32] :
      ( v1_pre_topc(k1_tex_2(A_31,B_32))
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_35])).

tff(c_41,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_42,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_41])).

tff(c_97,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(u1_struct_0(A_52),B_53) = u1_struct_0(k1_tex_2(A_52,B_53))
      | ~ m1_pre_topc(k1_tex_2(A_52,B_53),A_52)
      | ~ v1_pre_topc(k1_tex_2(A_52,B_53))
      | v2_struct_0(k1_tex_2(A_52,B_53))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_97])).

tff(c_102,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_42,c_99])).

tff(c_103,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_50,c_102])).

tff(c_24,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_104,plain,(
    ~ v2_tex_2(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_24])).

tff(c_116,plain,
    ( ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_104])).

tff(c_119,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_57,c_79,c_116])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_50,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:50:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.60  
% 2.39/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.60  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.39/1.60  
% 2.39/1.60  %Foreground sorts:
% 2.39/1.60  
% 2.39/1.60  
% 2.39/1.60  %Background operators:
% 2.39/1.60  
% 2.39/1.60  
% 2.39/1.60  %Foreground operators:
% 2.39/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.39/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.39/1.60  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.39/1.60  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.39/1.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.39/1.60  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.60  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.60  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.39/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.60  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.39/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.39/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.39/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.39/1.60  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.39/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.60  
% 2.39/1.62  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.39/1.62  tff(f_75, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.39/1.62  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.39/1.62  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v2_pre_topc(k1_tex_2(A, B)) => (v1_tdlat_3(k1_tex_2(A, B)) & v2_tdlat_3(k1_tex_2(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tex_2)).
% 2.39/1.62  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.39/1.62  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 2.39/1.62  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 2.39/1.62  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.39/1.62  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.39/1.62  tff(c_26, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.39/1.62  tff(c_43, plain, (![A_33, B_34]: (~v2_struct_0(k1_tex_2(A_33, B_34)) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.62  tff(c_46, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_43])).
% 2.39/1.62  tff(c_49, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_46])).
% 2.39/1.62  tff(c_50, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_49])).
% 2.39/1.62  tff(c_51, plain, (![A_35, B_36]: (m1_pre_topc(k1_tex_2(A_35, B_36), A_35) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~l1_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.62  tff(c_53, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_51])).
% 2.39/1.62  tff(c_56, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_53])).
% 2.39/1.62  tff(c_57, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_56])).
% 2.39/1.62  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.39/1.62  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.39/1.62  tff(c_60, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_57, c_2])).
% 2.39/1.62  tff(c_63, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_60])).
% 2.39/1.62  tff(c_72, plain, (![A_39, B_40]: (v1_tdlat_3(k1_tex_2(A_39, B_40)) | ~v2_pre_topc(k1_tex_2(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.39/1.62  tff(c_75, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_72])).
% 2.39/1.62  tff(c_78, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_63, c_75])).
% 2.39/1.62  tff(c_79, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_78])).
% 2.39/1.62  tff(c_4, plain, (![B_6, A_4]: (m1_subset_1(u1_struct_0(B_6), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.62  tff(c_80, plain, (![B_41, A_42]: (v2_tex_2(u1_struct_0(B_41), A_42) | ~v1_tdlat_3(B_41) | ~m1_subset_1(u1_struct_0(B_41), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_pre_topc(B_41, A_42) | v2_struct_0(B_41) | ~l1_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.39/1.62  tff(c_84, plain, (![B_6, A_4]: (v2_tex_2(u1_struct_0(B_6), A_4) | ~v1_tdlat_3(B_6) | v2_struct_0(B_6) | v2_struct_0(A_4) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_4, c_80])).
% 2.39/1.62  tff(c_35, plain, (![A_31, B_32]: (v1_pre_topc(k1_tex_2(A_31, B_32)) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.62  tff(c_38, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_35])).
% 2.39/1.62  tff(c_41, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 2.39/1.62  tff(c_42, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_41])).
% 2.39/1.62  tff(c_97, plain, (![A_52, B_53]: (k6_domain_1(u1_struct_0(A_52), B_53)=u1_struct_0(k1_tex_2(A_52, B_53)) | ~m1_pre_topc(k1_tex_2(A_52, B_53), A_52) | ~v1_pre_topc(k1_tex_2(A_52, B_53)) | v2_struct_0(k1_tex_2(A_52, B_53)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.39/1.62  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_57, c_97])).
% 2.39/1.62  tff(c_102, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_42, c_99])).
% 2.39/1.62  tff(c_103, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_50, c_102])).
% 2.39/1.62  tff(c_24, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.39/1.62  tff(c_104, plain, (~v2_tex_2(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_24])).
% 2.39/1.62  tff(c_116, plain, (~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84, c_104])).
% 2.39/1.62  tff(c_119, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_57, c_79, c_116])).
% 2.39/1.62  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_50, c_119])).
% 2.39/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.62  
% 2.39/1.62  Inference rules
% 2.39/1.62  ----------------------
% 2.39/1.62  #Ref     : 0
% 2.39/1.62  #Sup     : 14
% 2.39/1.62  #Fact    : 0
% 2.39/1.62  #Define  : 0
% 2.39/1.62  #Split   : 0
% 2.39/1.62  #Chain   : 0
% 2.39/1.62  #Close   : 0
% 2.39/1.62  
% 2.62/1.62  Ordering : KBO
% 2.62/1.62  
% 2.62/1.62  Simplification rules
% 2.62/1.62  ----------------------
% 2.62/1.62  #Subsume      : 2
% 2.62/1.62  #Demod        : 18
% 2.62/1.62  #Tautology    : 3
% 2.62/1.62  #SimpNegUnit  : 8
% 2.62/1.62  #BackRed      : 1
% 2.62/1.62  
% 2.62/1.62  #Partial instantiations: 0
% 2.62/1.62  #Strategies tried      : 1
% 2.62/1.62  
% 2.62/1.62  Timing (in seconds)
% 2.62/1.62  ----------------------
% 2.62/1.63  Preprocessing        : 0.53
% 2.62/1.63  Parsing              : 0.27
% 2.62/1.63  CNF conversion       : 0.04
% 2.62/1.63  Main loop            : 0.21
% 2.62/1.63  Inferencing          : 0.08
% 2.62/1.63  Reduction            : 0.07
% 2.62/1.63  Demodulation         : 0.05
% 2.62/1.63  BG Simplification    : 0.02
% 2.62/1.63  Subsumption          : 0.04
% 2.62/1.63  Abstraction          : 0.02
% 2.62/1.63  MUC search           : 0.00
% 2.62/1.63  Cooper               : 0.00
% 2.62/1.63  Total                : 0.79
% 2.62/1.63  Index Insertion      : 0.00
% 2.62/1.63  Index Deletion       : 0.00
% 2.62/1.63  Index Matching       : 0.00
% 2.62/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
