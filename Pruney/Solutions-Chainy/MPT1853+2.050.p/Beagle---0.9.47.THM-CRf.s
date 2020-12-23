%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:07 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 162 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  165 ( 463 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_52,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_119,plain,(
    ! [A_46,B_47] :
      ( m1_pre_topc(k1_tex_2(A_46,B_47),A_46)
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_121,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_119])).

tff(c_124,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_121])).

tff(c_125,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_124])).

tff(c_24,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_50,plain,(
    ! [A_27,B_28] :
      ( m1_pre_topc(k1_tex_2(A_27,B_28),A_27)
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_50])).

tff(c_55,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_52])).

tff(c_56,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_55])).

tff(c_34,plain,(
    ! [A_23,B_24] :
      ( ~ v2_struct_0(k1_tex_2(A_23,B_24))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_37,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_34])).

tff(c_40,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_37])).

tff(c_41,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_40])).

tff(c_42,plain,(
    ! [A_25,B_26] :
      ( v1_pre_topc(k1_tex_2(A_25,B_26))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_45,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_42])).

tff(c_48,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_45])).

tff(c_49,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_48])).

tff(c_74,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(u1_struct_0(A_40),B_41) = u1_struct_0(k1_tex_2(A_40,B_41))
      | ~ m1_pre_topc(k1_tex_2(A_40,B_41),A_40)
      | ~ v1_pre_topc(k1_tex_2(A_40,B_41))
      | v2_struct_0(k1_tex_2(A_40,B_41))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_74])).

tff(c_79,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_49,c_76])).

tff(c_80,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_41,c_79])).

tff(c_30,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_33,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30])).

tff(c_81,plain,(
    v1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_33])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( m1_subset_1(u1_struct_0(B_3),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [B_33,A_34] :
      ( v1_tex_2(B_33,A_34)
      | ~ v1_subset_1(u1_struct_0(B_33),u1_struct_0(A_34))
      | ~ m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_pre_topc(B_33,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_67,plain,(
    ! [B_3,A_1] :
      ( v1_tex_2(B_3,A_1)
      | ~ v1_subset_1(u1_struct_0(B_3),u1_struct_0(A_1))
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_93,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_67])).

tff(c_96,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56,c_93])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_96])).

tff(c_100,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_132,plain,(
    ! [B_52,A_53] :
      ( v1_subset_1(u1_struct_0(B_52),u1_struct_0(A_53))
      | ~ v1_tex_2(B_52,A_53)
      | ~ m1_subset_1(u1_struct_0(B_52),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_136,plain,(
    ! [B_3,A_1] :
      ( v1_subset_1(u1_struct_0(B_3),u1_struct_0(A_1))
      | ~ v1_tex_2(B_3,A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_132])).

tff(c_109,plain,(
    ! [A_44,B_45] :
      ( ~ v2_struct_0(k1_tex_2(A_44,B_45))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_109])).

tff(c_115,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_112])).

tff(c_116,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_115])).

tff(c_101,plain,(
    ! [A_42,B_43] :
      ( v1_pre_topc(k1_tex_2(A_42,B_43))
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l1_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_107,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_108,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_107])).

tff(c_143,plain,(
    ! [A_59,B_60] :
      ( k6_domain_1(u1_struct_0(A_59),B_60) = u1_struct_0(k1_tex_2(A_59,B_60))
      | ~ m1_pre_topc(k1_tex_2(A_59,B_60),A_59)
      | ~ v1_pre_topc(k1_tex_2(A_59,B_60))
      | v2_struct_0(k1_tex_2(A_59,B_60))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_145,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_125,c_143])).

tff(c_148,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_108,c_145])).

tff(c_149,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_116,c_148])).

tff(c_99,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_150,plain,(
    ~ v1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_99])).

tff(c_162,plain,
    ( ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_136,c_150])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_125,c_100,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:33:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.21  
% 2.20/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.21  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.20/1.21  
% 2.20/1.21  %Foreground sorts:
% 2.20/1.21  
% 2.20/1.21  
% 2.20/1.21  %Background operators:
% 2.20/1.21  
% 2.20/1.21  
% 2.20/1.21  %Foreground operators:
% 2.20/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.20/1.21  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.20/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.21  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.20/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.21  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.20/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.21  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.21  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.20/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.21  
% 2.20/1.22  tff(f_93, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 2.20/1.22  tff(f_66, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.20/1.22  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 2.20/1.22  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.20/1.22  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 2.20/1.22  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.22  tff(c_22, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.22  tff(c_18, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.22  tff(c_119, plain, (![A_46, B_47]: (m1_pre_topc(k1_tex_2(A_46, B_47), A_46) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.22  tff(c_121, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_119])).
% 2.20/1.22  tff(c_124, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_121])).
% 2.20/1.22  tff(c_125, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_22, c_124])).
% 2.20/1.22  tff(c_24, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.22  tff(c_32, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 2.20/1.22  tff(c_50, plain, (![A_27, B_28]: (m1_pre_topc(k1_tex_2(A_27, B_28), A_27) | ~m1_subset_1(B_28, u1_struct_0(A_27)) | ~l1_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.22  tff(c_52, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_50])).
% 2.20/1.22  tff(c_55, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_52])).
% 2.20/1.22  tff(c_56, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_22, c_55])).
% 2.20/1.22  tff(c_34, plain, (![A_23, B_24]: (~v2_struct_0(k1_tex_2(A_23, B_24)) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.22  tff(c_37, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_34])).
% 2.20/1.22  tff(c_40, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_37])).
% 2.20/1.22  tff(c_41, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_40])).
% 2.20/1.22  tff(c_42, plain, (![A_25, B_26]: (v1_pre_topc(k1_tex_2(A_25, B_26)) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.22  tff(c_45, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_42])).
% 2.20/1.22  tff(c_48, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_45])).
% 2.20/1.22  tff(c_49, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_48])).
% 2.20/1.22  tff(c_74, plain, (![A_40, B_41]: (k6_domain_1(u1_struct_0(A_40), B_41)=u1_struct_0(k1_tex_2(A_40, B_41)) | ~m1_pre_topc(k1_tex_2(A_40, B_41), A_40) | ~v1_pre_topc(k1_tex_2(A_40, B_41)) | v2_struct_0(k1_tex_2(A_40, B_41)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.22  tff(c_76, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_74])).
% 2.20/1.22  tff(c_79, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_49, c_76])).
% 2.20/1.22  tff(c_80, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_41, c_79])).
% 2.20/1.22  tff(c_30, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.22  tff(c_33, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_32, c_30])).
% 2.20/1.22  tff(c_81, plain, (v1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_33])).
% 2.20/1.22  tff(c_2, plain, (![B_3, A_1]: (m1_subset_1(u1_struct_0(B_3), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.22  tff(c_63, plain, (![B_33, A_34]: (v1_tex_2(B_33, A_34) | ~v1_subset_1(u1_struct_0(B_33), u1_struct_0(A_34)) | ~m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_pre_topc(B_33, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.22  tff(c_67, plain, (![B_3, A_1]: (v1_tex_2(B_3, A_1) | ~v1_subset_1(u1_struct_0(B_3), u1_struct_0(A_1)) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_63])).
% 2.20/1.22  tff(c_93, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_81, c_67])).
% 2.20/1.22  tff(c_96, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56, c_93])).
% 2.20/1.22  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_96])).
% 2.20/1.22  tff(c_100, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 2.20/1.22  tff(c_132, plain, (![B_52, A_53]: (v1_subset_1(u1_struct_0(B_52), u1_struct_0(A_53)) | ~v1_tex_2(B_52, A_53) | ~m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.22  tff(c_136, plain, (![B_3, A_1]: (v1_subset_1(u1_struct_0(B_3), u1_struct_0(A_1)) | ~v1_tex_2(B_3, A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_132])).
% 2.20/1.22  tff(c_109, plain, (![A_44, B_45]: (~v2_struct_0(k1_tex_2(A_44, B_45)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.22  tff(c_112, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_109])).
% 2.20/1.22  tff(c_115, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_112])).
% 2.20/1.22  tff(c_116, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_115])).
% 2.20/1.22  tff(c_101, plain, (![A_42, B_43]: (v1_pre_topc(k1_tex_2(A_42, B_43)) | ~m1_subset_1(B_43, u1_struct_0(A_42)) | ~l1_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.22  tff(c_104, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_101])).
% 2.20/1.22  tff(c_107, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_104])).
% 2.20/1.22  tff(c_108, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_107])).
% 2.20/1.22  tff(c_143, plain, (![A_59, B_60]: (k6_domain_1(u1_struct_0(A_59), B_60)=u1_struct_0(k1_tex_2(A_59, B_60)) | ~m1_pre_topc(k1_tex_2(A_59, B_60), A_59) | ~v1_pre_topc(k1_tex_2(A_59, B_60)) | v2_struct_0(k1_tex_2(A_59, B_60)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.22  tff(c_145, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_125, c_143])).
% 2.20/1.22  tff(c_148, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_108, c_145])).
% 2.20/1.22  tff(c_149, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_116, c_148])).
% 2.20/1.22  tff(c_99, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_24])).
% 2.20/1.22  tff(c_150, plain, (~v1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_99])).
% 2.20/1.22  tff(c_162, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_136, c_150])).
% 2.20/1.22  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_125, c_100, c_162])).
% 2.20/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.22  
% 2.20/1.22  Inference rules
% 2.20/1.22  ----------------------
% 2.20/1.22  #Ref     : 0
% 2.20/1.22  #Sup     : 22
% 2.20/1.22  #Fact    : 0
% 2.20/1.22  #Define  : 0
% 2.20/1.22  #Split   : 1
% 2.20/1.22  #Chain   : 0
% 2.20/1.22  #Close   : 0
% 2.20/1.22  
% 2.20/1.22  Ordering : KBO
% 2.20/1.22  
% 2.20/1.22  Simplification rules
% 2.20/1.22  ----------------------
% 2.20/1.22  #Subsume      : 4
% 2.20/1.22  #Demod        : 24
% 2.20/1.22  #Tautology    : 9
% 2.20/1.22  #SimpNegUnit  : 13
% 2.20/1.22  #BackRed      : 2
% 2.20/1.22  
% 2.20/1.22  #Partial instantiations: 0
% 2.20/1.22  #Strategies tried      : 1
% 2.20/1.23  
% 2.20/1.23  Timing (in seconds)
% 2.20/1.23  ----------------------
% 2.20/1.23  Preprocessing        : 0.30
% 2.20/1.23  Parsing              : 0.16
% 2.20/1.23  CNF conversion       : 0.02
% 2.20/1.23  Main loop            : 0.16
% 2.20/1.23  Inferencing          : 0.06
% 2.20/1.23  Reduction            : 0.05
% 2.20/1.23  Demodulation         : 0.03
% 2.20/1.23  BG Simplification    : 0.01
% 2.20/1.23  Subsumption          : 0.03
% 2.20/1.23  Abstraction          : 0.01
% 2.20/1.23  MUC search           : 0.00
% 2.20/1.23  Cooper               : 0.00
% 2.20/1.23  Total                : 0.50
% 2.20/1.23  Index Insertion      : 0.00
% 2.20/1.23  Index Deletion       : 0.00
% 2.20/1.23  Index Matching       : 0.00
% 2.20/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
