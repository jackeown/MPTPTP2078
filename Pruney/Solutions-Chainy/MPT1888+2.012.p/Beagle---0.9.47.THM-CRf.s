%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:22 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   99 (1599 expanded)
%              Number of leaves         :   29 ( 589 expanded)
%              Depth                    :   18
%              Number of atoms          :  234 (6472 expanded)
%              Number of equality atoms :   24 ( 646 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_domain_1 > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
                  | k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_82,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
               => k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_79,plain,(
    ! [A_50,B_51] :
      ( m1_pre_topc(k1_tex_2(A_50,B_51),A_50)
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_83,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_90,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_83])).

tff(c_91,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_90])).

tff(c_12,plain,(
    ! [B_13,A_11] :
      ( m1_subset_1(u1_struct_0(B_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_49,plain,(
    ! [A_46,B_47] :
      ( ~ v2_struct_0(k1_tex_2(A_46,B_47))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_58,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_52])).

tff(c_59,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_58])).

tff(c_64,plain,(
    ! [A_48,B_49] :
      ( v1_pre_topc(k1_tex_2(A_48,B_49))
      | ~ m1_subset_1(B_49,u1_struct_0(A_48))
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_67,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_73,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_67])).

tff(c_74,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_73])).

tff(c_81,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_79])).

tff(c_86,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81])).

tff(c_87,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_86])).

tff(c_140,plain,(
    ! [A_72,B_73] :
      ( k6_domain_1(u1_struct_0(A_72),B_73) = u1_struct_0(k1_tex_2(A_72,B_73))
      | ~ m1_pre_topc(k1_tex_2(A_72,B_73),A_72)
      | ~ v1_pre_topc(k1_tex_2(A_72,B_73))
      | v2_struct_0(k1_tex_2(A_72,B_73))
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_144,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_140])).

tff(c_151,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_74,c_144])).

tff(c_152,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0(k1_tex_2('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_59,c_151])).

tff(c_55,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_62,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_55])).

tff(c_63,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_62])).

tff(c_70,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_77,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_70])).

tff(c_78,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_77])).

tff(c_142,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_91,c_140])).

tff(c_147,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_78,c_142])).

tff(c_148,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_63,c_147])).

tff(c_28,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_153,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_28])).

tff(c_174,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_153])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k2_pre_topc(A_55,B_56),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_105,plain,(
    ! [A_57,A_58,B_59] :
      ( m1_subset_1(A_57,u1_struct_0(A_58))
      | ~ r2_hidden(A_57,k2_pre_topc(A_58,B_59))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_112,plain,(
    ! [A_58,B_59,B_2] :
      ( m1_subset_1('#skF_1'(k2_pre_topc(A_58,B_59),B_2),u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | r1_xboole_0(k2_pre_topc(A_58,B_59),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_26,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_154,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_26])).

tff(c_173,plain,(
    k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))) != k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_154])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_36,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_183,plain,(
    ! [A_75,C_76,B_77] :
      ( k2_pre_topc(A_75,k6_domain_1(u1_struct_0(A_75),C_76)) = k2_pre_topc(A_75,k6_domain_1(u1_struct_0(A_75),B_77))
      | ~ r2_hidden(B_77,k2_pre_topc(A_75,k6_domain_1(u1_struct_0(A_75),C_76)))
      | ~ m1_subset_1(C_76,u1_struct_0(A_75))
      | ~ m1_subset_1(B_77,u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | ~ v3_tdlat_3(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_494,plain,(
    ! [A_125,A_126,C_127] :
      ( k2_pre_topc(A_125,k6_domain_1(u1_struct_0(A_125),'#skF_1'(A_126,k2_pre_topc(A_125,k6_domain_1(u1_struct_0(A_125),C_127))))) = k2_pre_topc(A_125,k6_domain_1(u1_struct_0(A_125),C_127))
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ m1_subset_1('#skF_1'(A_126,k2_pre_topc(A_125,k6_domain_1(u1_struct_0(A_125),C_127))),u1_struct_0(A_125))
      | ~ l1_pre_topc(A_125)
      | ~ v3_tdlat_3(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125)
      | r1_xboole_0(A_126,k2_pre_topc(A_125,k6_domain_1(u1_struct_0(A_125),C_127))) ) ),
    inference(resolution,[status(thm)],[c_4,c_183])).

tff(c_577,plain,(
    ! [A_126] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_126,k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))))) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_126,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_xboole_0(A_126,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_494])).

tff(c_602,plain,(
    ! [A_126] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_126,k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))))) = k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))
      | ~ m1_subset_1('#skF_1'(A_126,k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_xboole_0(A_126,k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_38,c_36,c_34,c_152,c_30,c_152,c_577])).

tff(c_607,plain,(
    ! [A_128] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_128,k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))))) = k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))
      | ~ m1_subset_1('#skF_1'(A_128,k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))),u1_struct_0('#skF_2'))
      | r1_xboole_0(A_128,k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_602])).

tff(c_260,plain,(
    ! [A_101,C_102,B_103] :
      ( k2_pre_topc(A_101,k6_domain_1(u1_struct_0(A_101),'#skF_1'(k2_pre_topc(A_101,k6_domain_1(u1_struct_0(A_101),C_102)),B_103))) = k2_pre_topc(A_101,k6_domain_1(u1_struct_0(A_101),C_102))
      | ~ m1_subset_1(C_102,u1_struct_0(A_101))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc(A_101,k6_domain_1(u1_struct_0(A_101),C_102)),B_103),u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ v3_tdlat_3(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101)
      | r1_xboole_0(k2_pre_topc(A_101,k6_domain_1(u1_struct_0(A_101),C_102)),B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_292,plain,(
    ! [B_103] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),B_103))) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),B_103),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_260])).

tff(c_299,plain,(
    ! [B_103] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),B_103))) = k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),B_103),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_38,c_36,c_34,c_148,c_32,c_148,c_292])).

tff(c_300,plain,(
    ! [B_103] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),B_103))) = k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),B_103),u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),B_103) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_299])).

tff(c_621,plain,
    ( k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))) = k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))),u1_struct_0('#skF_2'))
    | r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4'))))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))),u1_struct_0('#skF_2'))
    | r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_300])).

tff(c_681,plain,
    ( ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_174,c_173,c_621])).

tff(c_723,plain,(
    ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_681])).

tff(c_726,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))) ),
    inference(resolution,[status(thm)],[c_112,c_723])).

tff(c_732,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_726])).

tff(c_733,plain,(
    ~ m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_732])).

tff(c_856,plain,
    ( ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_733])).

tff(c_860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_91,c_856])).

tff(c_861,plain,(
    ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_681])).

tff(c_865,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))) ),
    inference(resolution,[status(thm)],[c_112,c_861])).

tff(c_871,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | r1_xboole_0(k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_3'))),k2_pre_topc('#skF_2',u1_struct_0(k1_tex_2('#skF_2','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_865])).

tff(c_872,plain,(
    ~ m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_871])).

tff(c_879,plain,
    ( ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_872])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_91,c_879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.56  
% 3.17/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.57  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_domain_1 > k2_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.17/1.57  
% 3.17/1.57  %Foreground sorts:
% 3.17/1.57  
% 3.17/1.57  
% 3.17/1.57  %Background operators:
% 3.17/1.57  
% 3.17/1.57  
% 3.17/1.57  %Foreground operators:
% 3.17/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.17/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.17/1.57  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.17/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.17/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.57  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.17/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.57  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.17/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.57  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.17/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.17/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.17/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.17/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.57  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.17/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.57  
% 3.17/1.58  tff(f_135, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tex_2)).
% 3.17/1.58  tff(f_96, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.17/1.58  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.17/1.58  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 3.17/1.58  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.17/1.58  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.17/1.58  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.17/1.58  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tex_2)).
% 3.17/1.58  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.17/1.58  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.17/1.58  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.17/1.58  tff(c_79, plain, (![A_50, B_51]: (m1_pre_topc(k1_tex_2(A_50, B_51), A_50) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.17/1.58  tff(c_83, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_79])).
% 3.17/1.58  tff(c_90, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_83])).
% 3.17/1.58  tff(c_91, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_90])).
% 3.17/1.58  tff(c_12, plain, (![B_13, A_11]: (m1_subset_1(u1_struct_0(B_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.58  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.17/1.58  tff(c_49, plain, (![A_46, B_47]: (~v2_struct_0(k1_tex_2(A_46, B_47)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.17/1.58  tff(c_52, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_49])).
% 3.17/1.58  tff(c_58, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_52])).
% 3.17/1.58  tff(c_59, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_58])).
% 3.17/1.58  tff(c_64, plain, (![A_48, B_49]: (v1_pre_topc(k1_tex_2(A_48, B_49)) | ~m1_subset_1(B_49, u1_struct_0(A_48)) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.17/1.58  tff(c_67, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_64])).
% 3.17/1.58  tff(c_73, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_67])).
% 3.17/1.58  tff(c_74, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_73])).
% 3.17/1.58  tff(c_81, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_79])).
% 3.17/1.58  tff(c_86, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81])).
% 3.17/1.58  tff(c_87, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_86])).
% 3.17/1.58  tff(c_140, plain, (![A_72, B_73]: (k6_domain_1(u1_struct_0(A_72), B_73)=u1_struct_0(k1_tex_2(A_72, B_73)) | ~m1_pre_topc(k1_tex_2(A_72, B_73), A_72) | ~v1_pre_topc(k1_tex_2(A_72, B_73)) | v2_struct_0(k1_tex_2(A_72, B_73)) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.17/1.58  tff(c_144, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_87, c_140])).
% 3.17/1.58  tff(c_151, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_74, c_144])).
% 3.17/1.58  tff(c_152, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_59, c_151])).
% 3.17/1.58  tff(c_55, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_49])).
% 3.17/1.58  tff(c_62, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_55])).
% 3.17/1.58  tff(c_63, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_62])).
% 3.17/1.58  tff(c_70, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_64])).
% 3.17/1.58  tff(c_77, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_70])).
% 3.17/1.58  tff(c_78, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_77])).
% 3.17/1.58  tff(c_142, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_91, c_140])).
% 3.17/1.58  tff(c_147, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_78, c_142])).
% 3.17/1.58  tff(c_148, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_63, c_147])).
% 3.17/1.58  tff(c_28, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.17/1.58  tff(c_153, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_28])).
% 3.17/1.58  tff(c_174, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_153])).
% 3.17/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.58  tff(c_101, plain, (![A_55, B_56]: (m1_subset_1(k2_pre_topc(A_55, B_56), k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.58  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.17/1.58  tff(c_105, plain, (![A_57, A_58, B_59]: (m1_subset_1(A_57, u1_struct_0(A_58)) | ~r2_hidden(A_57, k2_pre_topc(A_58, B_59)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_101, c_8])).
% 3.17/1.58  tff(c_112, plain, (![A_58, B_59, B_2]: (m1_subset_1('#skF_1'(k2_pre_topc(A_58, B_59), B_2), u1_struct_0(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | r1_xboole_0(k2_pre_topc(A_58, B_59), B_2))), inference(resolution, [status(thm)], [c_6, c_105])).
% 3.17/1.58  tff(c_26, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.17/1.58  tff(c_154, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_26])).
% 3.17/1.58  tff(c_173, plain, (k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3')))!=k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_154])).
% 3.17/1.58  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.17/1.58  tff(c_36, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.17/1.58  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.58  tff(c_183, plain, (![A_75, C_76, B_77]: (k2_pre_topc(A_75, k6_domain_1(u1_struct_0(A_75), C_76))=k2_pre_topc(A_75, k6_domain_1(u1_struct_0(A_75), B_77)) | ~r2_hidden(B_77, k2_pre_topc(A_75, k6_domain_1(u1_struct_0(A_75), C_76))) | ~m1_subset_1(C_76, u1_struct_0(A_75)) | ~m1_subset_1(B_77, u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | ~v3_tdlat_3(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.17/1.58  tff(c_494, plain, (![A_125, A_126, C_127]: (k2_pre_topc(A_125, k6_domain_1(u1_struct_0(A_125), '#skF_1'(A_126, k2_pre_topc(A_125, k6_domain_1(u1_struct_0(A_125), C_127)))))=k2_pre_topc(A_125, k6_domain_1(u1_struct_0(A_125), C_127)) | ~m1_subset_1(C_127, u1_struct_0(A_125)) | ~m1_subset_1('#skF_1'(A_126, k2_pre_topc(A_125, k6_domain_1(u1_struct_0(A_125), C_127))), u1_struct_0(A_125)) | ~l1_pre_topc(A_125) | ~v3_tdlat_3(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125) | r1_xboole_0(A_126, k2_pre_topc(A_125, k6_domain_1(u1_struct_0(A_125), C_127))))), inference(resolution, [status(thm)], [c_4, c_183])).
% 3.17/1.58  tff(c_577, plain, (![A_126]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_126, k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_126, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_xboole_0(A_126, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_152, c_494])).
% 3.17/1.58  tff(c_602, plain, (![A_126]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_126, k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))))=k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_1'(A_126, k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_xboole_0(A_126, k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_38, c_36, c_34, c_152, c_30, c_152, c_577])).
% 3.17/1.58  tff(c_607, plain, (![A_128]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_128, k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))))=k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_1'(A_128, k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), u1_struct_0('#skF_2')) | r1_xboole_0(A_128, k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))))), inference(negUnitSimplification, [status(thm)], [c_40, c_602])).
% 3.17/1.58  tff(c_260, plain, (![A_101, C_102, B_103]: (k2_pre_topc(A_101, k6_domain_1(u1_struct_0(A_101), '#skF_1'(k2_pre_topc(A_101, k6_domain_1(u1_struct_0(A_101), C_102)), B_103)))=k2_pre_topc(A_101, k6_domain_1(u1_struct_0(A_101), C_102)) | ~m1_subset_1(C_102, u1_struct_0(A_101)) | ~m1_subset_1('#skF_1'(k2_pre_topc(A_101, k6_domain_1(u1_struct_0(A_101), C_102)), B_103), u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | ~v3_tdlat_3(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101) | r1_xboole_0(k2_pre_topc(A_101, k6_domain_1(u1_struct_0(A_101), C_102)), B_103))), inference(resolution, [status(thm)], [c_6, c_183])).
% 3.17/1.58  tff(c_292, plain, (![B_103]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), B_103)))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), B_103), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), B_103))), inference(superposition, [status(thm), theory('equality')], [c_148, c_260])).
% 3.17/1.58  tff(c_299, plain, (![B_103]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), B_103)))=k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), B_103), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), B_103))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_38, c_36, c_34, c_148, c_32, c_148, c_292])).
% 3.17/1.58  tff(c_300, plain, (![B_103]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), B_103)))=k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), B_103), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), B_103))), inference(negUnitSimplification, [status(thm)], [c_40, c_299])).
% 3.17/1.58  tff(c_621, plain, (k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3')))=k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_607, c_300])).
% 3.17/1.58  tff(c_681, plain, (~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_174, c_174, c_173, c_621])).
% 3.17/1.58  tff(c_723, plain, (~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_681])).
% 3.17/1.58  tff(c_726, plain, (~m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))), inference(resolution, [status(thm)], [c_112, c_723])).
% 3.17/1.58  tff(c_732, plain, (~m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_726])).
% 3.17/1.58  tff(c_733, plain, (~m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_174, c_732])).
% 3.17/1.58  tff(c_856, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_733])).
% 3.17/1.58  tff(c_860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_91, c_856])).
% 3.17/1.58  tff(c_861, plain, (~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4')))), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_681])).
% 3.17/1.58  tff(c_865, plain, (~m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))), inference(resolution, [status(thm)], [c_112, c_861])).
% 3.17/1.58  tff(c_871, plain, (~m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_xboole_0(k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), k2_pre_topc('#skF_2', u1_struct_0(k1_tex_2('#skF_2', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_865])).
% 3.17/1.58  tff(c_872, plain, (~m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_174, c_871])).
% 3.17/1.58  tff(c_879, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_872])).
% 3.17/1.58  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_91, c_879])).
% 3.17/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.58  
% 3.17/1.58  Inference rules
% 3.17/1.58  ----------------------
% 3.17/1.58  #Ref     : 2
% 3.17/1.58  #Sup     : 164
% 3.17/1.58  #Fact    : 0
% 3.17/1.58  #Define  : 0
% 3.17/1.58  #Split   : 1
% 3.17/1.58  #Chain   : 0
% 3.17/1.58  #Close   : 0
% 3.17/1.58  
% 3.17/1.58  Ordering : KBO
% 3.17/1.58  
% 3.17/1.58  Simplification rules
% 3.17/1.58  ----------------------
% 3.17/1.58  #Subsume      : 0
% 3.17/1.58  #Demod        : 170
% 3.17/1.58  #Tautology    : 22
% 3.17/1.58  #SimpNegUnit  : 70
% 3.17/1.58  #BackRed      : 2
% 3.17/1.58  
% 3.17/1.58  #Partial instantiations: 0
% 3.17/1.58  #Strategies tried      : 1
% 3.17/1.58  
% 3.17/1.58  Timing (in seconds)
% 3.17/1.58  ----------------------
% 3.17/1.59  Preprocessing        : 0.31
% 3.17/1.59  Parsing              : 0.16
% 3.17/1.59  CNF conversion       : 0.02
% 3.17/1.59  Main loop            : 0.44
% 3.17/1.59  Inferencing          : 0.16
% 3.17/1.59  Reduction            : 0.15
% 3.17/1.59  Demodulation         : 0.10
% 3.17/1.59  BG Simplification    : 0.03
% 3.17/1.59  Subsumption          : 0.08
% 3.17/1.59  Abstraction          : 0.03
% 3.17/1.59  MUC search           : 0.00
% 3.17/1.59  Cooper               : 0.00
% 3.17/1.59  Total                : 0.78
% 3.17/1.59  Index Insertion      : 0.00
% 3.17/1.59  Index Deletion       : 0.00
% 3.17/1.59  Index Matching       : 0.00
% 3.17/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
