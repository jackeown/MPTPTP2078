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
% DateTime   : Thu Dec  3 10:23:50 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  195 (42708 expanded)
%              Number of leaves         :   35 (14588 expanded)
%              Depth                    :   30
%              Number of atoms          :  783 (123839 expanded)
%              Number of equality atoms :  149 (20144 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v3_tops_2,type,(
    v3_tops_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_tops_2(C,A,B)
                 => v3_tops_2(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & v5_pre_topc(C,A,B)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                  & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_16,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_55,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_16,c_55])).

tff(c_68,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_60])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_67,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_69,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_42])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_88,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_85])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_44])).

tff(c_79,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70])).

tff(c_106,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_funct_1(k2_funct_1(C_48))
      | k2_relset_1(A_49,B_50,C_48) != B_50
      | ~ v2_funct_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(C_48,A_49,B_50)
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_106])).

tff(c_112,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_109])).

tff(c_113,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_40,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_150,plain,(
    ! [C_60,A_61,B_62] :
      ( v2_funct_1(C_60)
      | ~ v3_tops_2(C_60,A_61,B_62)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61),u1_struct_0(B_62))))
      | ~ v1_funct_2(C_60,u1_struct_0(A_61),u1_struct_0(B_62))
      | ~ v1_funct_1(C_60)
      | ~ l1_pre_topc(B_62)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_157,plain,(
    ! [C_60,B_62] :
      ( v2_funct_1(C_60)
      | ~ v3_tops_2(C_60,'#skF_1',B_62)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_62))))
      | ~ v1_funct_2(C_60,u1_struct_0('#skF_1'),u1_struct_0(B_62))
      | ~ v1_funct_1(C_60)
      | ~ l1_pre_topc(B_62)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_150])).

tff(c_215,plain,(
    ! [C_70,B_71] :
      ( v2_funct_1(C_70)
      | ~ v3_tops_2(C_70,'#skF_1',B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_71))))
      | ~ v1_funct_2(C_70,k2_struct_0('#skF_1'),u1_struct_0(B_71))
      | ~ v1_funct_1(C_70)
      | ~ l1_pre_topc(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_157])).

tff(c_225,plain,(
    ! [C_70] :
      ( v2_funct_1(C_70)
      | ~ v3_tops_2(C_70,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_70,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_70)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_215])).

tff(c_231,plain,(
    ! [C_72] :
      ( v2_funct_1(C_72)
      | ~ v3_tops_2(C_72,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_72,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_225])).

tff(c_238,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_231])).

tff(c_242,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_40,c_238])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_242])).

tff(c_246,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_705,plain,(
    ! [C_140,A_141,B_142] :
      ( v5_pre_topc(C_140,A_141,B_142)
      | ~ v3_tops_2(C_140,A_141,B_142)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_140,u1_struct_0(A_141),u1_struct_0(B_142))
      | ~ v1_funct_1(C_140)
      | ~ l1_pre_topc(B_142)
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_721,plain,(
    ! [C_140,A_141] :
      ( v5_pre_topc(C_140,A_141,'#skF_2')
      | ~ v3_tops_2(C_140,A_141,'#skF_2')
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_140,u1_struct_0(A_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_140)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_705])).

tff(c_825,plain,(
    ! [C_155,A_156] :
      ( v5_pre_topc(C_155,A_156,'#skF_2')
      | ~ v3_tops_2(C_155,A_156,'#skF_2')
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_155,u1_struct_0(A_156),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_155)
      | ~ l1_pre_topc(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_721])).

tff(c_832,plain,(
    ! [C_155] :
      ( v5_pre_topc(C_155,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_155,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_155,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_155)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_825])).

tff(c_867,plain,(
    ! [C_160] :
      ( v5_pre_topc(C_160,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_160,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_160,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_832])).

tff(c_874,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_867])).

tff(c_878,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_40,c_874])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_245,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_247,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_497,plain,(
    ! [A_110,B_111,C_112] :
      ( k2_relset_1(u1_struct_0(A_110),u1_struct_0(B_111),C_112) = k2_struct_0(B_111)
      | ~ v3_tops_2(C_112,A_110,B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_112,u1_struct_0(A_110),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ l1_pre_topc(B_111)
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_504,plain,(
    ! [B_111,C_112] :
      ( k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_111),C_112) = k2_struct_0(B_111)
      | ~ v3_tops_2(C_112,'#skF_1',B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_112,u1_struct_0('#skF_1'),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ l1_pre_topc(B_111)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_497])).

tff(c_589,plain,(
    ! [B_122,C_123] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_122),C_123) = k2_struct_0(B_122)
      | ~ v3_tops_2(C_123,'#skF_1',B_122)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_122))))
      | ~ v1_funct_2(C_123,k2_struct_0('#skF_1'),u1_struct_0(B_122))
      | ~ v1_funct_1(C_123)
      | ~ l1_pre_topc(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_68,c_504])).

tff(c_599,plain,(
    ! [C_123] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_123) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_123,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_123,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_123)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_589])).

tff(c_605,plain,(
    ! [C_124] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_124) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_124,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_124,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_67,c_599])).

tff(c_612,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_605])).

tff(c_616,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_40,c_612])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_616])).

tff(c_620,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_619,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_621,plain,(
    ! [C_125,B_126,A_127] :
      ( v1_funct_2(k2_funct_1(C_125),B_126,A_127)
      | k2_relset_1(A_127,B_126,C_125) != B_126
      | ~ v2_funct_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_2(C_125,A_127,B_126)
      | ~ v1_funct_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_624,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_621])).

tff(c_627,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_246,c_624])).

tff(c_633,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_627])).

tff(c_634,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_tops_2(A_128,B_129,C_130) = k2_funct_1(C_130)
      | ~ v2_funct_1(C_130)
      | k2_relset_1(A_128,B_129,C_130) != B_129
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_2(C_130,A_128,B_129)
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_637,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_634])).

tff(c_640,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_620,c_246,c_637])).

tff(c_1209,plain,(
    ! [A_203,B_204,C_205] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_203),u1_struct_0(B_204),C_205))
      | ~ v2_funct_1(C_205)
      | k2_relset_1(u1_struct_0(A_203),u1_struct_0(B_204),C_205) != k2_struct_0(B_204)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203),u1_struct_0(B_204))))
      | ~ v1_funct_2(C_205,u1_struct_0(A_203),u1_struct_0(B_204))
      | ~ v1_funct_1(C_205)
      | ~ l1_struct_0(B_204)
      | ~ l1_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1222,plain,(
    ! [B_204,C_205] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0(B_204),C_205))
      | ~ v2_funct_1(C_205)
      | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_204),C_205) != k2_struct_0(B_204)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_204))))
      | ~ v1_funct_2(C_205,u1_struct_0('#skF_2'),u1_struct_0(B_204))
      | ~ v1_funct_1(C_205)
      | ~ l1_struct_0(B_204)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1209])).

tff(c_1229,plain,(
    ! [B_204,C_205] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(B_204),C_205))
      | ~ v2_funct_1(C_205)
      | k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_204),C_205) != k2_struct_0(B_204)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_204))))
      | ~ v1_funct_2(C_205,k2_struct_0('#skF_2'),u1_struct_0(B_204))
      | ~ v1_funct_1(C_205)
      | ~ l1_struct_0(B_204)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_67,c_1222])).

tff(c_1296,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1229])).

tff(c_1342,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1296])).

tff(c_1346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1342])).

tff(c_1354,plain,(
    ! [B_221,C_222] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(B_221),C_222))
      | ~ v2_funct_1(C_222)
      | k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_221),C_222) != k2_struct_0(B_221)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_221))))
      | ~ v1_funct_2(C_222,k2_struct_0('#skF_2'),u1_struct_0(B_221))
      | ~ v1_funct_1(C_222)
      | ~ l1_struct_0(B_221) ) ),
    inference(splitRight,[status(thm)],[c_1229])).

tff(c_1361,plain,(
    ! [C_222] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),C_222))
      | ~ v2_funct_1(C_222)
      | k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),C_222) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_222,k2_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_222)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1354])).

tff(c_1366,plain,(
    ! [C_222] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_222))
      | ~ v2_funct_1(C_222)
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_222) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_222,k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_222)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_1361])).

tff(c_1375,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1366])).

tff(c_1378,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1375])).

tff(c_1382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1378])).

tff(c_1384,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1366])).

tff(c_1348,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1229])).

tff(c_1225,plain,(
    ! [A_203,C_205] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_203),u1_struct_0('#skF_2'),C_205))
      | ~ v2_funct_1(C_205)
      | k2_relset_1(u1_struct_0(A_203),u1_struct_0('#skF_2'),C_205) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_205,u1_struct_0(A_203),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_205)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1209])).

tff(c_1230,plain,(
    ! [A_203,C_205] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_203),k2_struct_0('#skF_2'),C_205))
      | ~ v2_funct_1(C_205)
      | k2_relset_1(u1_struct_0(A_203),k2_struct_0('#skF_2'),C_205) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_205,u1_struct_0(A_203),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_205)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_67,c_1225])).

tff(c_1398,plain,(
    ! [A_225,C_226] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_225),k2_struct_0('#skF_2'),C_226))
      | ~ v2_funct_1(C_226)
      | k2_relset_1(u1_struct_0(A_225),k2_struct_0('#skF_2'),C_226) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_226,u1_struct_0(A_225),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_226)
      | ~ l1_struct_0(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1230])).

tff(c_1405,plain,(
    ! [C_226] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_226))
      | ~ v2_funct_1(C_226)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_226) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_226,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_226)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1398])).

tff(c_1465,plain,(
    ! [C_230] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_230))
      | ~ v2_funct_1(C_230)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_230) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_230,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_68,c_68,c_68,c_1405])).

tff(c_1472,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1465])).

tff(c_1476,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_620,c_246,c_640,c_1472])).

tff(c_646,plain,(
    ! [C_131,B_132,A_133] :
      ( m1_subset_1(k2_funct_1(C_131),k1_zfmisc_1(k2_zfmisc_1(B_132,A_133)))
      | k2_relset_1(A_133,B_132,C_131) != B_132
      | ~ v2_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132)))
      | ~ v1_funct_2(C_131,A_133,B_132)
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_funct_1(k2_funct_1(C_9))
      | k2_relset_1(A_7,B_8,C_9) != B_8
      | ~ v2_funct_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1626,plain,(
    ! [C_243,B_244,A_245] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_243)))
      | k2_relset_1(B_244,A_245,k2_funct_1(C_243)) != A_245
      | ~ v2_funct_1(k2_funct_1(C_243))
      | ~ v1_funct_2(k2_funct_1(C_243),B_244,A_245)
      | ~ v1_funct_1(k2_funct_1(C_243))
      | k2_relset_1(A_245,B_244,C_243) != B_244
      | ~ v2_funct_1(C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_2(C_243,A_245,B_244)
      | ~ v1_funct_1(C_243) ) ),
    inference(resolution,[status(thm)],[c_646,c_12])).

tff(c_1632,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1626])).

tff(c_1636,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_246,c_620,c_619,c_633,c_1476,c_1632])).

tff(c_1637,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1636])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1566,plain,(
    ! [B_239,A_240,C_241] :
      ( k2_relset_1(u1_struct_0(B_239),u1_struct_0(A_240),k2_tops_2(u1_struct_0(A_240),u1_struct_0(B_239),C_241)) = k2_struct_0(A_240)
      | ~ v2_funct_1(C_241)
      | k2_relset_1(u1_struct_0(A_240),u1_struct_0(B_239),C_241) != k2_struct_0(B_239)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240),u1_struct_0(B_239))))
      | ~ v1_funct_2(C_241,u1_struct_0(A_240),u1_struct_0(B_239))
      | ~ v1_funct_1(C_241)
      | ~ l1_struct_0(B_239)
      | v2_struct_0(B_239)
      | ~ l1_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1596,plain,(
    ! [A_240,C_241] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_240),k2_tops_2(u1_struct_0(A_240),k2_struct_0('#skF_2'),C_241)) = k2_struct_0(A_240)
      | ~ v2_funct_1(C_241)
      | k2_relset_1(u1_struct_0(A_240),u1_struct_0('#skF_2'),C_241) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_241,u1_struct_0(A_240),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_241)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1566])).

tff(c_1615,plain,(
    ! [A_240,C_241] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_240),k2_tops_2(u1_struct_0(A_240),k2_struct_0('#skF_2'),C_241)) = k2_struct_0(A_240)
      | ~ v2_funct_1(C_241)
      | k2_relset_1(u1_struct_0(A_240),k2_struct_0('#skF_2'),C_241) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_241,u1_struct_0(A_240),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_241)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_67,c_67,c_67,c_67,c_1596])).

tff(c_1649,plain,(
    ! [A_249,C_250] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_249),k2_tops_2(u1_struct_0(A_249),k2_struct_0('#skF_2'),C_250)) = k2_struct_0(A_249)
      | ~ v2_funct_1(C_250)
      | k2_relset_1(u1_struct_0(A_249),k2_struct_0('#skF_2'),C_250) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_250,u1_struct_0(A_249),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_250)
      | ~ l1_struct_0(A_249) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1615])).

tff(c_1658,plain,(
    ! [C_250] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_250)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_250)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_250) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_250,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_250)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1649])).

tff(c_1678,plain,(
    ! [C_251] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_251)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_251)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_251) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_251,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_68,c_68,c_68,c_68,c_1658])).

tff(c_1687,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_1678])).

tff(c_1691,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_82,c_620,c_246,c_1687])).

tff(c_1693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1637,c_1691])).

tff(c_1695,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1636])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( v1_funct_2(k2_funct_1(C_9),B_8,A_7)
      | k2_relset_1(A_7,B_8,C_9) != B_8
      | ~ v2_funct_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_663,plain,(
    ! [C_131,A_133,B_132] :
      ( v1_funct_2(k2_funct_1(k2_funct_1(C_131)),A_133,B_132)
      | k2_relset_1(B_132,A_133,k2_funct_1(C_131)) != A_133
      | ~ v2_funct_1(k2_funct_1(C_131))
      | ~ v1_funct_2(k2_funct_1(C_131),B_132,A_133)
      | ~ v1_funct_1(k2_funct_1(C_131))
      | k2_relset_1(A_133,B_132,C_131) != B_132
      | ~ v2_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132)))
      | ~ v1_funct_2(C_131,A_133,B_132)
      | ~ v1_funct_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_646,c_10])).

tff(c_38,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_81,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67,c_38])).

tff(c_641,plain,(
    ~ v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_81])).

tff(c_1694,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1636])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( m1_subset_1(k2_funct_1(C_9),k1_zfmisc_1(k2_zfmisc_1(B_8,A_7)))
      | k2_relset_1(A_7,B_8,C_9) != B_8
      | ~ v2_funct_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2989,plain,(
    ! [C_349,A_350,B_351] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(C_349))))
      | k2_relset_1(A_350,B_351,k2_funct_1(k2_funct_1(C_349))) != B_351
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(C_349)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(C_349)),A_350,B_351)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(C_349)))
      | k2_relset_1(B_351,A_350,k2_funct_1(C_349)) != A_350
      | ~ v2_funct_1(k2_funct_1(C_349))
      | ~ v1_funct_2(k2_funct_1(C_349),B_351,A_350)
      | ~ v1_funct_1(k2_funct_1(C_349))
      | k2_relset_1(A_350,B_351,C_349) != B_351
      | ~ v2_funct_1(C_349)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351)))
      | ~ v1_funct_2(C_349,A_350,B_351)
      | ~ v1_funct_1(C_349) ) ),
    inference(resolution,[status(thm)],[c_8,c_1626])).

tff(c_3189,plain,(
    ! [C_378,A_379,B_380] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(C_378))))
      | k2_relset_1(A_379,B_380,k2_funct_1(k2_funct_1(C_378))) != B_380
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(C_378)))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(C_378)))
      | k2_relset_1(B_380,A_379,k2_funct_1(C_378)) != A_379
      | ~ v2_funct_1(k2_funct_1(C_378))
      | ~ v1_funct_2(k2_funct_1(C_378),B_380,A_379)
      | ~ v1_funct_1(k2_funct_1(C_378))
      | k2_relset_1(A_379,B_380,C_378) != B_380
      | ~ v2_funct_1(C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380)))
      | ~ v1_funct_2(C_378,A_379,B_380)
      | ~ v1_funct_1(C_378) ) ),
    inference(resolution,[status(thm)],[c_663,c_2989])).

tff(c_3195,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3189])).

tff(c_3200,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_246,c_620,c_619,c_633,c_1476,c_1695,c_1694,c_3195])).

tff(c_3201,plain,(
    ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3200])).

tff(c_3225,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3201])).

tff(c_3228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46,c_246,c_246,c_3225])).

tff(c_3229,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_3200])).

tff(c_3236,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3229])).

tff(c_3239,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3236])).

tff(c_3242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46,c_246,c_620,c_3239])).

tff(c_3244,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3229])).

tff(c_1414,plain,(
    ! [B_227,A_228,C_229] :
      ( k1_relset_1(u1_struct_0(B_227),u1_struct_0(A_228),k2_tops_2(u1_struct_0(A_228),u1_struct_0(B_227),C_229)) = k2_struct_0(B_227)
      | ~ v2_funct_1(C_229)
      | k2_relset_1(u1_struct_0(A_228),u1_struct_0(B_227),C_229) != k2_struct_0(B_227)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_228),u1_struct_0(B_227))))
      | ~ v1_funct_2(C_229,u1_struct_0(A_228),u1_struct_0(B_227))
      | ~ v1_funct_1(C_229)
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227)
      | ~ l1_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1435,plain,(
    ! [A_228,C_229] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_228),k2_tops_2(u1_struct_0(A_228),u1_struct_0('#skF_2'),C_229)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_229)
      | k2_relset_1(u1_struct_0(A_228),u1_struct_0('#skF_2'),C_229) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_228),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_229,u1_struct_0(A_228),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_229)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1414])).

tff(c_1456,plain,(
    ! [A_228,C_229] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_228),k2_tops_2(u1_struct_0(A_228),k2_struct_0('#skF_2'),C_229)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_229)
      | k2_relset_1(u1_struct_0(A_228),k2_struct_0('#skF_2'),C_229) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_228),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_229,u1_struct_0(A_228),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_229)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_67,c_67,c_67,c_67,c_1435])).

tff(c_1495,plain,(
    ! [A_233,C_234] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_233),k2_tops_2(u1_struct_0(A_233),k2_struct_0('#skF_2'),C_234)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_234)
      | k2_relset_1(u1_struct_0(A_233),k2_struct_0('#skF_2'),C_234) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_233),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_234,u1_struct_0(A_233),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_234)
      | ~ l1_struct_0(A_233) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1456])).

tff(c_1504,plain,(
    ! [C_234] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_234)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_234)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_234) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_234,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_234)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1495])).

tff(c_1548,plain,(
    ! [C_238] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_238)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_238)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_238) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_238,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_68,c_68,c_68,c_68,c_1504])).

tff(c_1557,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_1548])).

tff(c_1561,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_82,c_620,c_246,c_1557])).

tff(c_1071,plain,(
    ! [A_185,B_186,C_187] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_185),u1_struct_0(B_186),C_187),B_186,A_185)
      | ~ v3_tops_2(C_187,A_185,B_186)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_185),u1_struct_0(B_186))))
      | ~ v1_funct_2(C_187,u1_struct_0(A_185),u1_struct_0(B_186))
      | ~ v1_funct_1(C_187)
      | ~ l1_pre_topc(B_186)
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1082,plain,(
    ! [A_185,C_187] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_185),u1_struct_0('#skF_2'),C_187),'#skF_2',A_185)
      | ~ v3_tops_2(C_187,A_185,'#skF_2')
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_185),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_187,u1_struct_0(A_185),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_187)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1071])).

tff(c_1184,plain,(
    ! [A_200,C_201] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_200),k2_struct_0('#skF_2'),C_201),'#skF_2',A_200)
      | ~ v3_tops_2(C_201,A_200,'#skF_2')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_200),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_201,u1_struct_0(A_200),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc(A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_67,c_1082])).

tff(c_1189,plain,(
    ! [C_201] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_201),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_201,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_201,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1184])).

tff(c_1197,plain,(
    ! [C_202] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_202),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_202,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_202,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_68,c_1189])).

tff(c_1204,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1197])).

tff(c_1208,plain,(
    v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_40,c_640,c_1204])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_tops_2(A_12,B_13,C_14) = k2_funct_1(C_14)
      | ~ v2_funct_1(C_14)
      | k2_relset_1(A_12,B_13,C_14) != B_13
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1862,plain,(
    ! [B_269,A_270,C_271] :
      ( k2_tops_2(B_269,A_270,k2_funct_1(C_271)) = k2_funct_1(k2_funct_1(C_271))
      | ~ v2_funct_1(k2_funct_1(C_271))
      | k2_relset_1(B_269,A_270,k2_funct_1(C_271)) != A_270
      | ~ v1_funct_2(k2_funct_1(C_271),B_269,A_270)
      | ~ v1_funct_1(k2_funct_1(C_271))
      | k2_relset_1(A_270,B_269,C_271) != B_269
      | ~ v2_funct_1(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_270,B_269)))
      | ~ v1_funct_2(C_271,A_270,B_269)
      | ~ v1_funct_1(C_271) ) ),
    inference(resolution,[status(thm)],[c_646,c_18])).

tff(c_1868,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1862])).

tff(c_1872,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_246,c_620,c_619,c_633,c_1695,c_1476,c_1868])).

tff(c_3230,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3200])).

tff(c_3074,plain,(
    ! [A_362,B_363,C_364] :
      ( k2_tops_2(A_362,B_363,k2_funct_1(k2_funct_1(C_364))) = k2_funct_1(k2_funct_1(k2_funct_1(C_364)))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(C_364)))
      | k2_relset_1(A_362,B_363,k2_funct_1(k2_funct_1(C_364))) != B_363
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(C_364)),A_362,B_363)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(C_364)))
      | k2_relset_1(B_363,A_362,k2_funct_1(C_364)) != A_362
      | ~ v2_funct_1(k2_funct_1(C_364))
      | ~ v1_funct_2(k2_funct_1(C_364),B_363,A_362)
      | ~ v1_funct_1(k2_funct_1(C_364))
      | k2_relset_1(A_362,B_363,C_364) != B_363
      | ~ v2_funct_1(C_364)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(A_362,B_363)))
      | ~ v1_funct_2(C_364,A_362,B_363)
      | ~ v1_funct_1(C_364) ) ),
    inference(resolution,[status(thm)],[c_8,c_1862])).

tff(c_3532,plain,(
    ! [A_416,B_417,C_418] :
      ( k2_tops_2(A_416,B_417,k2_funct_1(k2_funct_1(C_418))) = k2_funct_1(k2_funct_1(k2_funct_1(C_418)))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(C_418)))
      | k2_relset_1(A_416,B_417,k2_funct_1(k2_funct_1(C_418))) != B_417
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(C_418)))
      | k2_relset_1(B_417,A_416,k2_funct_1(C_418)) != A_416
      | ~ v2_funct_1(k2_funct_1(C_418))
      | ~ v1_funct_2(k2_funct_1(C_418),B_417,A_416)
      | ~ v1_funct_1(k2_funct_1(C_418))
      | k2_relset_1(A_416,B_417,C_418) != B_417
      | ~ v2_funct_1(C_418)
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_416,B_417)))
      | ~ v1_funct_2(C_418,A_416,B_417)
      | ~ v1_funct_1(C_418) ) ),
    inference(resolution,[status(thm)],[c_663,c_3074])).

tff(c_3541,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3532])).

tff(c_3546,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_246,c_620,c_619,c_633,c_1476,c_1695,c_1694,c_3244,c_3230,c_3541])).

tff(c_3560,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3546])).

tff(c_3570,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46,c_246,c_640,c_3560])).

tff(c_3656,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_8,A_7)))
      | k2_relset_1(A_7,B_8,k2_funct_1(k2_funct_1('#skF_3'))) != B_8
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_7,B_8)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3570,c_8])).

tff(c_4603,plain,(
    ! [B_425,A_426] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_425,A_426)))
      | k2_relset_1(A_426,B_425,k2_funct_1(k2_funct_1('#skF_3'))) != B_425
      | ~ m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_426,B_425)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_426,B_425) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_3230,c_3656])).

tff(c_4617,plain,(
    ! [B_425,A_426] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_425,A_426)))
      | k2_relset_1(A_426,B_425,k2_funct_1(k2_funct_1('#skF_3'))) != B_425
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_426,B_425)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_426,B_425)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4603])).

tff(c_4627,plain,(
    ! [B_427,A_428] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_427,A_428)))
      | k2_relset_1(A_428,B_427,k2_funct_1(k2_funct_1('#skF_3'))) != B_427
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_428,B_427)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_428,B_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46,c_246,c_4617])).

tff(c_1696,plain,(
    ! [C_252,A_253,B_254] :
      ( v3_tops_2(C_252,A_253,B_254)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_253),u1_struct_0(B_254),C_252),B_254,A_253)
      | ~ v5_pre_topc(C_252,A_253,B_254)
      | ~ v2_funct_1(C_252)
      | k2_relset_1(u1_struct_0(A_253),u1_struct_0(B_254),C_252) != k2_struct_0(B_254)
      | k1_relset_1(u1_struct_0(A_253),u1_struct_0(B_254),C_252) != k2_struct_0(A_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_253),u1_struct_0(B_254))))
      | ~ v1_funct_2(C_252,u1_struct_0(A_253),u1_struct_0(B_254))
      | ~ v1_funct_1(C_252)
      | ~ l1_pre_topc(B_254)
      | ~ l1_pre_topc(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1700,plain,(
    ! [C_252,A_253] :
      ( v3_tops_2(C_252,A_253,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_253),k2_struct_0('#skF_1'),C_252),'#skF_1',A_253)
      | ~ v5_pre_topc(C_252,A_253,'#skF_1')
      | ~ v2_funct_1(C_252)
      | k2_relset_1(u1_struct_0(A_253),u1_struct_0('#skF_1'),C_252) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_253),u1_struct_0('#skF_1'),C_252) != k2_struct_0(A_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_253),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_252,u1_struct_0(A_253),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_252)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1696])).

tff(c_3065,plain,(
    ! [C_360,A_361] :
      ( v3_tops_2(C_360,A_361,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_361),k2_struct_0('#skF_1'),C_360),'#skF_1',A_361)
      | ~ v5_pre_topc(C_360,A_361,'#skF_1')
      | ~ v2_funct_1(C_360)
      | k2_relset_1(u1_struct_0(A_361),k2_struct_0('#skF_1'),C_360) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_361),k2_struct_0('#skF_1'),C_360) != k2_struct_0(A_361)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_360,u1_struct_0(A_361),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_360)
      | ~ l1_pre_topc(A_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_68,c_68,c_68,c_1700])).

tff(c_3069,plain,(
    ! [C_360] :
      ( v3_tops_2(C_360,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_360),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_360,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_360)
      | k2_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_360) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_360) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_360,u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_360)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_3065])).

tff(c_3073,plain,(
    ! [C_360] :
      ( v3_tops_2(C_360,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_360),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_360,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_360)
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_360) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_360) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_360,k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_67,c_67,c_67,c_3069])).

tff(c_4677,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4627,c_3073])).

tff(c_5115,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3244,c_619,c_633,c_1561,c_1695,c_1476,c_1208,c_1872,c_4677])).

tff(c_5116,plain,
    ( ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_5115])).

tff(c_5468,plain,(
    ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5116])).

tff(c_5471,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_663,c_5468])).

tff(c_5478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_82,c_246,c_620,c_619,c_633,c_1476,c_1695,c_5471])).

tff(c_5479,plain,(
    ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_5116])).

tff(c_5483,plain,
    ( ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5479])).

tff(c_5486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46,c_246,c_878,c_5483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:04:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.82  
% 7.97/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.83  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.97/2.83  
% 7.97/2.83  %Foreground sorts:
% 7.97/2.83  
% 7.97/2.83  
% 7.97/2.83  %Background operators:
% 7.97/2.83  
% 7.97/2.83  
% 7.97/2.83  %Foreground operators:
% 7.97/2.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.97/2.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.97/2.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.97/2.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.97/2.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.97/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/2.83  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 7.97/2.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.97/2.83  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 7.97/2.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.97/2.83  tff('#skF_2', type, '#skF_2': $i).
% 7.97/2.83  tff('#skF_3', type, '#skF_3': $i).
% 7.97/2.83  tff('#skF_1', type, '#skF_1': $i).
% 7.97/2.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.97/2.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.97/2.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.97/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/2.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.97/2.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.97/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/2.83  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.97/2.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.97/2.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.97/2.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.97/2.83  
% 7.97/2.87  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.97/2.87  tff(f_163, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 7.97/2.87  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.97/2.87  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.97/2.87  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.97/2.87  tff(f_58, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.97/2.87  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 7.97/2.87  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 7.97/2.87  tff(f_78, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 7.97/2.87  tff(f_143, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 7.97/2.87  tff(f_125, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 7.97/2.87  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.97/2.87  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.97/2.87  tff(c_16, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.97/2.87  tff(c_55, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.97/2.87  tff(c_60, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_16, c_55])).
% 7.97/2.87  tff(c_68, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_60])).
% 7.97/2.87  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.97/2.87  tff(c_67, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_60])).
% 7.97/2.87  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.97/2.87  tff(c_69, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_42])).
% 7.97/2.87  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69])).
% 7.97/2.87  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.97/2.87  tff(c_85, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_82, c_2])).
% 7.97/2.87  tff(c_88, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_85])).
% 7.97/2.87  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.97/2.87  tff(c_44, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.97/2.87  tff(c_70, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_44])).
% 7.97/2.87  tff(c_79, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70])).
% 7.97/2.87  tff(c_106, plain, (![C_48, A_49, B_50]: (v1_funct_1(k2_funct_1(C_48)) | k2_relset_1(A_49, B_50, C_48)!=B_50 | ~v2_funct_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(C_48, A_49, B_50) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.87  tff(c_109, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_106])).
% 7.97/2.87  tff(c_112, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_109])).
% 7.97/2.87  tff(c_113, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_112])).
% 7.97/2.87  tff(c_40, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.97/2.87  tff(c_150, plain, (![C_60, A_61, B_62]: (v2_funct_1(C_60) | ~v3_tops_2(C_60, A_61, B_62) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61), u1_struct_0(B_62)))) | ~v1_funct_2(C_60, u1_struct_0(A_61), u1_struct_0(B_62)) | ~v1_funct_1(C_60) | ~l1_pre_topc(B_62) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.97/2.87  tff(c_157, plain, (![C_60, B_62]: (v2_funct_1(C_60) | ~v3_tops_2(C_60, '#skF_1', B_62) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_62)))) | ~v1_funct_2(C_60, u1_struct_0('#skF_1'), u1_struct_0(B_62)) | ~v1_funct_1(C_60) | ~l1_pre_topc(B_62) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_150])).
% 7.97/2.87  tff(c_215, plain, (![C_70, B_71]: (v2_funct_1(C_70) | ~v3_tops_2(C_70, '#skF_1', B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_71)))) | ~v1_funct_2(C_70, k2_struct_0('#skF_1'), u1_struct_0(B_71)) | ~v1_funct_1(C_70) | ~l1_pre_topc(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_157])).
% 7.97/2.87  tff(c_225, plain, (![C_70]: (v2_funct_1(C_70) | ~v3_tops_2(C_70, '#skF_1', '#skF_2') | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_70, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_70) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_215])).
% 7.97/2.87  tff(c_231, plain, (![C_72]: (v2_funct_1(C_72) | ~v3_tops_2(C_72, '#skF_1', '#skF_2') | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_72, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_72))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_225])).
% 7.97/2.87  tff(c_238, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_231])).
% 7.97/2.87  tff(c_242, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_40, c_238])).
% 7.97/2.87  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_242])).
% 7.97/2.87  tff(c_246, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_112])).
% 7.97/2.87  tff(c_705, plain, (![C_140, A_141, B_142]: (v5_pre_topc(C_140, A_141, B_142) | ~v3_tops_2(C_140, A_141, B_142) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141), u1_struct_0(B_142)))) | ~v1_funct_2(C_140, u1_struct_0(A_141), u1_struct_0(B_142)) | ~v1_funct_1(C_140) | ~l1_pre_topc(B_142) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.97/2.87  tff(c_721, plain, (![C_140, A_141]: (v5_pre_topc(C_140, A_141, '#skF_2') | ~v3_tops_2(C_140, A_141, '#skF_2') | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_140, u1_struct_0(A_141), u1_struct_0('#skF_2')) | ~v1_funct_1(C_140) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_141))), inference(superposition, [status(thm), theory('equality')], [c_67, c_705])).
% 7.97/2.87  tff(c_825, plain, (![C_155, A_156]: (v5_pre_topc(C_155, A_156, '#skF_2') | ~v3_tops_2(C_155, A_156, '#skF_2') | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_155, u1_struct_0(A_156), k2_struct_0('#skF_2')) | ~v1_funct_1(C_155) | ~l1_pre_topc(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_721])).
% 7.97/2.87  tff(c_832, plain, (![C_155]: (v5_pre_topc(C_155, '#skF_1', '#skF_2') | ~v3_tops_2(C_155, '#skF_1', '#skF_2') | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_155, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_155) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_825])).
% 7.97/2.87  tff(c_867, plain, (![C_160]: (v5_pre_topc(C_160, '#skF_1', '#skF_2') | ~v3_tops_2(C_160, '#skF_1', '#skF_2') | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_160, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_160))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_832])).
% 7.97/2.87  tff(c_874, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_867])).
% 7.97/2.87  tff(c_878, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_40, c_874])).
% 7.97/2.87  tff(c_6, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.97/2.87  tff(c_245, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_112])).
% 7.97/2.87  tff(c_247, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_245])).
% 7.97/2.87  tff(c_497, plain, (![A_110, B_111, C_112]: (k2_relset_1(u1_struct_0(A_110), u1_struct_0(B_111), C_112)=k2_struct_0(B_111) | ~v3_tops_2(C_112, A_110, B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_111)))) | ~v1_funct_2(C_112, u1_struct_0(A_110), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~l1_pre_topc(B_111) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.97/2.87  tff(c_504, plain, (![B_111, C_112]: (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_111), C_112)=k2_struct_0(B_111) | ~v3_tops_2(C_112, '#skF_1', B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_111)))) | ~v1_funct_2(C_112, u1_struct_0('#skF_1'), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~l1_pre_topc(B_111) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_497])).
% 7.97/2.87  tff(c_589, plain, (![B_122, C_123]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_122), C_123)=k2_struct_0(B_122) | ~v3_tops_2(C_123, '#skF_1', B_122) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_122)))) | ~v1_funct_2(C_123, k2_struct_0('#skF_1'), u1_struct_0(B_122)) | ~v1_funct_1(C_123) | ~l1_pre_topc(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_68, c_504])).
% 7.97/2.87  tff(c_599, plain, (![C_123]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_123)=k2_struct_0('#skF_2') | ~v3_tops_2(C_123, '#skF_1', '#skF_2') | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_123, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_123) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_589])).
% 7.97/2.87  tff(c_605, plain, (![C_124]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_124)=k2_struct_0('#skF_2') | ~v3_tops_2(C_124, '#skF_1', '#skF_2') | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_124, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_124))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_67, c_599])).
% 7.97/2.87  tff(c_612, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_605])).
% 7.97/2.87  tff(c_616, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_40, c_612])).
% 7.97/2.87  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_616])).
% 7.97/2.87  tff(c_620, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_245])).
% 7.97/2.87  tff(c_619, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_245])).
% 7.97/2.87  tff(c_621, plain, (![C_125, B_126, A_127]: (v1_funct_2(k2_funct_1(C_125), B_126, A_127) | k2_relset_1(A_127, B_126, C_125)!=B_126 | ~v2_funct_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_2(C_125, A_127, B_126) | ~v1_funct_1(C_125))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.87  tff(c_624, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_621])).
% 7.97/2.87  tff(c_627, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_246, c_624])).
% 7.97/2.87  tff(c_633, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_620, c_627])).
% 7.97/2.87  tff(c_634, plain, (![A_128, B_129, C_130]: (k2_tops_2(A_128, B_129, C_130)=k2_funct_1(C_130) | ~v2_funct_1(C_130) | k2_relset_1(A_128, B_129, C_130)!=B_129 | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_2(C_130, A_128, B_129) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.97/2.87  tff(c_637, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_634])).
% 7.97/2.87  tff(c_640, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_620, c_246, c_637])).
% 7.97/2.87  tff(c_1209, plain, (![A_203, B_204, C_205]: (v2_funct_1(k2_tops_2(u1_struct_0(A_203), u1_struct_0(B_204), C_205)) | ~v2_funct_1(C_205) | k2_relset_1(u1_struct_0(A_203), u1_struct_0(B_204), C_205)!=k2_struct_0(B_204) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203), u1_struct_0(B_204)))) | ~v1_funct_2(C_205, u1_struct_0(A_203), u1_struct_0(B_204)) | ~v1_funct_1(C_205) | ~l1_struct_0(B_204) | ~l1_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.97/2.87  tff(c_1222, plain, (![B_204, C_205]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0(B_204), C_205)) | ~v2_funct_1(C_205) | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_204), C_205)!=k2_struct_0(B_204) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_204)))) | ~v1_funct_2(C_205, u1_struct_0('#skF_2'), u1_struct_0(B_204)) | ~v1_funct_1(C_205) | ~l1_struct_0(B_204) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1209])).
% 7.97/2.87  tff(c_1229, plain, (![B_204, C_205]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(B_204), C_205)) | ~v2_funct_1(C_205) | k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_204), C_205)!=k2_struct_0(B_204) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_204)))) | ~v1_funct_2(C_205, k2_struct_0('#skF_2'), u1_struct_0(B_204)) | ~v1_funct_1(C_205) | ~l1_struct_0(B_204) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_67, c_1222])).
% 7.97/2.87  tff(c_1296, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1229])).
% 7.97/2.87  tff(c_1342, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1296])).
% 7.97/2.87  tff(c_1346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1342])).
% 7.97/2.87  tff(c_1354, plain, (![B_221, C_222]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(B_221), C_222)) | ~v2_funct_1(C_222) | k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_221), C_222)!=k2_struct_0(B_221) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_221)))) | ~v1_funct_2(C_222, k2_struct_0('#skF_2'), u1_struct_0(B_221)) | ~v1_funct_1(C_222) | ~l1_struct_0(B_221))), inference(splitRight, [status(thm)], [c_1229])).
% 7.97/2.87  tff(c_1361, plain, (![C_222]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), C_222)) | ~v2_funct_1(C_222) | k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), C_222)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_222, k2_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(C_222) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1354])).
% 7.97/2.87  tff(c_1366, plain, (![C_222]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_222)) | ~v2_funct_1(C_222) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_222)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_222, k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_222) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_1361])).
% 7.97/2.87  tff(c_1375, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1366])).
% 7.97/2.87  tff(c_1378, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1375])).
% 7.97/2.87  tff(c_1382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1378])).
% 7.97/2.87  tff(c_1384, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1366])).
% 7.97/2.87  tff(c_1348, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1229])).
% 7.97/2.87  tff(c_1225, plain, (![A_203, C_205]: (v2_funct_1(k2_tops_2(u1_struct_0(A_203), u1_struct_0('#skF_2'), C_205)) | ~v2_funct_1(C_205) | k2_relset_1(u1_struct_0(A_203), u1_struct_0('#skF_2'), C_205)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_205, u1_struct_0(A_203), u1_struct_0('#skF_2')) | ~v1_funct_1(C_205) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_203))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1209])).
% 7.97/2.87  tff(c_1230, plain, (![A_203, C_205]: (v2_funct_1(k2_tops_2(u1_struct_0(A_203), k2_struct_0('#skF_2'), C_205)) | ~v2_funct_1(C_205) | k2_relset_1(u1_struct_0(A_203), k2_struct_0('#skF_2'), C_205)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_205, u1_struct_0(A_203), k2_struct_0('#skF_2')) | ~v1_funct_1(C_205) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_203))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_67, c_1225])).
% 7.97/2.87  tff(c_1398, plain, (![A_225, C_226]: (v2_funct_1(k2_tops_2(u1_struct_0(A_225), k2_struct_0('#skF_2'), C_226)) | ~v2_funct_1(C_226) | k2_relset_1(u1_struct_0(A_225), k2_struct_0('#skF_2'), C_226)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_226, u1_struct_0(A_225), k2_struct_0('#skF_2')) | ~v1_funct_1(C_226) | ~l1_struct_0(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1230])).
% 7.97/2.87  tff(c_1405, plain, (![C_226]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_226)) | ~v2_funct_1(C_226) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_226)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_226, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_226) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1398])).
% 7.97/2.87  tff(c_1465, plain, (![C_230]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_230)) | ~v2_funct_1(C_230) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_230)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_230, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_230))), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_68, c_68, c_68, c_1405])).
% 7.97/2.87  tff(c_1472, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1465])).
% 7.97/2.87  tff(c_1476, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_620, c_246, c_640, c_1472])).
% 7.97/2.87  tff(c_646, plain, (![C_131, B_132, A_133]: (m1_subset_1(k2_funct_1(C_131), k1_zfmisc_1(k2_zfmisc_1(B_132, A_133))) | k2_relset_1(A_133, B_132, C_131)!=B_132 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))) | ~v1_funct_2(C_131, A_133, B_132) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.87  tff(c_12, plain, (![C_9, A_7, B_8]: (v1_funct_1(k2_funct_1(C_9)) | k2_relset_1(A_7, B_8, C_9)!=B_8 | ~v2_funct_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.87  tff(c_1626, plain, (![C_243, B_244, A_245]: (v1_funct_1(k2_funct_1(k2_funct_1(C_243))) | k2_relset_1(B_244, A_245, k2_funct_1(C_243))!=A_245 | ~v2_funct_1(k2_funct_1(C_243)) | ~v1_funct_2(k2_funct_1(C_243), B_244, A_245) | ~v1_funct_1(k2_funct_1(C_243)) | k2_relset_1(A_245, B_244, C_243)!=B_244 | ~v2_funct_1(C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_2(C_243, A_245, B_244) | ~v1_funct_1(C_243))), inference(resolution, [status(thm)], [c_646, c_12])).
% 7.97/2.87  tff(c_1632, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1626])).
% 7.97/2.87  tff(c_1636, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_246, c_620, c_619, c_633, c_1476, c_1632])).
% 7.97/2.87  tff(c_1637, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1636])).
% 7.97/2.87  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.97/2.87  tff(c_1566, plain, (![B_239, A_240, C_241]: (k2_relset_1(u1_struct_0(B_239), u1_struct_0(A_240), k2_tops_2(u1_struct_0(A_240), u1_struct_0(B_239), C_241))=k2_struct_0(A_240) | ~v2_funct_1(C_241) | k2_relset_1(u1_struct_0(A_240), u1_struct_0(B_239), C_241)!=k2_struct_0(B_239) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240), u1_struct_0(B_239)))) | ~v1_funct_2(C_241, u1_struct_0(A_240), u1_struct_0(B_239)) | ~v1_funct_1(C_241) | ~l1_struct_0(B_239) | v2_struct_0(B_239) | ~l1_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.97/2.87  tff(c_1596, plain, (![A_240, C_241]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_240), k2_tops_2(u1_struct_0(A_240), k2_struct_0('#skF_2'), C_241))=k2_struct_0(A_240) | ~v2_funct_1(C_241) | k2_relset_1(u1_struct_0(A_240), u1_struct_0('#skF_2'), C_241)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_241, u1_struct_0(A_240), u1_struct_0('#skF_2')) | ~v1_funct_1(C_241) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_240))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1566])).
% 7.97/2.87  tff(c_1615, plain, (![A_240, C_241]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_240), k2_tops_2(u1_struct_0(A_240), k2_struct_0('#skF_2'), C_241))=k2_struct_0(A_240) | ~v2_funct_1(C_241) | k2_relset_1(u1_struct_0(A_240), k2_struct_0('#skF_2'), C_241)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_241, u1_struct_0(A_240), k2_struct_0('#skF_2')) | ~v1_funct_1(C_241) | v2_struct_0('#skF_2') | ~l1_struct_0(A_240))), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_67, c_67, c_67, c_67, c_1596])).
% 7.97/2.87  tff(c_1649, plain, (![A_249, C_250]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_249), k2_tops_2(u1_struct_0(A_249), k2_struct_0('#skF_2'), C_250))=k2_struct_0(A_249) | ~v2_funct_1(C_250) | k2_relset_1(u1_struct_0(A_249), k2_struct_0('#skF_2'), C_250)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_250, u1_struct_0(A_249), k2_struct_0('#skF_2')) | ~v1_funct_1(C_250) | ~l1_struct_0(A_249))), inference(negUnitSimplification, [status(thm)], [c_50, c_1615])).
% 7.97/2.87  tff(c_1658, plain, (![C_250]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_250))=k2_struct_0('#skF_1') | ~v2_funct_1(C_250) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_250)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_250, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_250) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1649])).
% 7.97/2.87  tff(c_1678, plain, (![C_251]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_251))=k2_struct_0('#skF_1') | ~v2_funct_1(C_251) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_251)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_251, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_251))), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_68, c_68, c_68, c_68, c_1658])).
% 7.97/2.87  tff(c_1687, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_640, c_1678])).
% 7.97/2.87  tff(c_1691, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_82, c_620, c_246, c_1687])).
% 7.97/2.87  tff(c_1693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1637, c_1691])).
% 7.97/2.87  tff(c_1695, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1636])).
% 7.97/2.87  tff(c_10, plain, (![C_9, B_8, A_7]: (v1_funct_2(k2_funct_1(C_9), B_8, A_7) | k2_relset_1(A_7, B_8, C_9)!=B_8 | ~v2_funct_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.87  tff(c_663, plain, (![C_131, A_133, B_132]: (v1_funct_2(k2_funct_1(k2_funct_1(C_131)), A_133, B_132) | k2_relset_1(B_132, A_133, k2_funct_1(C_131))!=A_133 | ~v2_funct_1(k2_funct_1(C_131)) | ~v1_funct_2(k2_funct_1(C_131), B_132, A_133) | ~v1_funct_1(k2_funct_1(C_131)) | k2_relset_1(A_133, B_132, C_131)!=B_132 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))) | ~v1_funct_2(C_131, A_133, B_132) | ~v1_funct_1(C_131))), inference(resolution, [status(thm)], [c_646, c_10])).
% 7.97/2.87  tff(c_38, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.97/2.87  tff(c_81, plain, (~v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67, c_38])).
% 7.97/2.87  tff(c_641, plain, (~v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_640, c_81])).
% 7.97/2.87  tff(c_1694, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1636])).
% 7.97/2.87  tff(c_8, plain, (![C_9, B_8, A_7]: (m1_subset_1(k2_funct_1(C_9), k1_zfmisc_1(k2_zfmisc_1(B_8, A_7))) | k2_relset_1(A_7, B_8, C_9)!=B_8 | ~v2_funct_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.87  tff(c_2989, plain, (![C_349, A_350, B_351]: (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(C_349)))) | k2_relset_1(A_350, B_351, k2_funct_1(k2_funct_1(C_349)))!=B_351 | ~v2_funct_1(k2_funct_1(k2_funct_1(C_349))) | ~v1_funct_2(k2_funct_1(k2_funct_1(C_349)), A_350, B_351) | ~v1_funct_1(k2_funct_1(k2_funct_1(C_349))) | k2_relset_1(B_351, A_350, k2_funct_1(C_349))!=A_350 | ~v2_funct_1(k2_funct_1(C_349)) | ~v1_funct_2(k2_funct_1(C_349), B_351, A_350) | ~v1_funct_1(k2_funct_1(C_349)) | k2_relset_1(A_350, B_351, C_349)!=B_351 | ~v2_funct_1(C_349) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_350, B_351))) | ~v1_funct_2(C_349, A_350, B_351) | ~v1_funct_1(C_349))), inference(resolution, [status(thm)], [c_8, c_1626])).
% 7.97/2.87  tff(c_3189, plain, (![C_378, A_379, B_380]: (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(C_378)))) | k2_relset_1(A_379, B_380, k2_funct_1(k2_funct_1(C_378)))!=B_380 | ~v2_funct_1(k2_funct_1(k2_funct_1(C_378))) | ~v1_funct_1(k2_funct_1(k2_funct_1(C_378))) | k2_relset_1(B_380, A_379, k2_funct_1(C_378))!=A_379 | ~v2_funct_1(k2_funct_1(C_378)) | ~v1_funct_2(k2_funct_1(C_378), B_380, A_379) | ~v1_funct_1(k2_funct_1(C_378)) | k2_relset_1(A_379, B_380, C_378)!=B_380 | ~v2_funct_1(C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))) | ~v1_funct_2(C_378, A_379, B_380) | ~v1_funct_1(C_378))), inference(resolution, [status(thm)], [c_663, c_2989])).
% 7.97/2.87  tff(c_3195, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3189])).
% 7.97/2.87  tff(c_3200, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_246, c_620, c_619, c_633, c_1476, c_1695, c_1694, c_3195])).
% 7.97/2.87  tff(c_3201, plain, (~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_3200])).
% 7.97/2.87  tff(c_3225, plain, (~v2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_3201])).
% 7.97/2.87  tff(c_3228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_46, c_246, c_246, c_3225])).
% 7.97/2.87  tff(c_3229, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_3200])).
% 7.97/2.87  tff(c_3236, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3229])).
% 7.97/2.87  tff(c_3239, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_3236])).
% 7.97/2.87  tff(c_3242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_46, c_246, c_620, c_3239])).
% 7.97/2.87  tff(c_3244, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3229])).
% 7.97/2.87  tff(c_1414, plain, (![B_227, A_228, C_229]: (k1_relset_1(u1_struct_0(B_227), u1_struct_0(A_228), k2_tops_2(u1_struct_0(A_228), u1_struct_0(B_227), C_229))=k2_struct_0(B_227) | ~v2_funct_1(C_229) | k2_relset_1(u1_struct_0(A_228), u1_struct_0(B_227), C_229)!=k2_struct_0(B_227) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_228), u1_struct_0(B_227)))) | ~v1_funct_2(C_229, u1_struct_0(A_228), u1_struct_0(B_227)) | ~v1_funct_1(C_229) | ~l1_struct_0(B_227) | v2_struct_0(B_227) | ~l1_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.97/2.87  tff(c_1435, plain, (![A_228, C_229]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_228), k2_tops_2(u1_struct_0(A_228), u1_struct_0('#skF_2'), C_229))=k2_struct_0('#skF_2') | ~v2_funct_1(C_229) | k2_relset_1(u1_struct_0(A_228), u1_struct_0('#skF_2'), C_229)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_228), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_229, u1_struct_0(A_228), u1_struct_0('#skF_2')) | ~v1_funct_1(C_229) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_228))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1414])).
% 7.97/2.87  tff(c_1456, plain, (![A_228, C_229]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_228), k2_tops_2(u1_struct_0(A_228), k2_struct_0('#skF_2'), C_229))=k2_struct_0('#skF_2') | ~v2_funct_1(C_229) | k2_relset_1(u1_struct_0(A_228), k2_struct_0('#skF_2'), C_229)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_228), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_229, u1_struct_0(A_228), k2_struct_0('#skF_2')) | ~v1_funct_1(C_229) | v2_struct_0('#skF_2') | ~l1_struct_0(A_228))), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_67, c_67, c_67, c_67, c_1435])).
% 7.97/2.87  tff(c_1495, plain, (![A_233, C_234]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_233), k2_tops_2(u1_struct_0(A_233), k2_struct_0('#skF_2'), C_234))=k2_struct_0('#skF_2') | ~v2_funct_1(C_234) | k2_relset_1(u1_struct_0(A_233), k2_struct_0('#skF_2'), C_234)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_233), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_234, u1_struct_0(A_233), k2_struct_0('#skF_2')) | ~v1_funct_1(C_234) | ~l1_struct_0(A_233))), inference(negUnitSimplification, [status(thm)], [c_50, c_1456])).
% 7.97/2.87  tff(c_1504, plain, (![C_234]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_234))=k2_struct_0('#skF_2') | ~v2_funct_1(C_234) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_234)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_234, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_234) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1495])).
% 7.97/2.87  tff(c_1548, plain, (![C_238]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_238))=k2_struct_0('#skF_2') | ~v2_funct_1(C_238) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_238)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_238, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_238))), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_68, c_68, c_68, c_68, c_1504])).
% 7.97/2.87  tff(c_1557, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_640, c_1548])).
% 7.97/2.87  tff(c_1561, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_82, c_620, c_246, c_1557])).
% 7.97/2.87  tff(c_1071, plain, (![A_185, B_186, C_187]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_185), u1_struct_0(B_186), C_187), B_186, A_185) | ~v3_tops_2(C_187, A_185, B_186) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_185), u1_struct_0(B_186)))) | ~v1_funct_2(C_187, u1_struct_0(A_185), u1_struct_0(B_186)) | ~v1_funct_1(C_187) | ~l1_pre_topc(B_186) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.97/2.87  tff(c_1082, plain, (![A_185, C_187]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_185), u1_struct_0('#skF_2'), C_187), '#skF_2', A_185) | ~v3_tops_2(C_187, A_185, '#skF_2') | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_185), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_187, u1_struct_0(A_185), u1_struct_0('#skF_2')) | ~v1_funct_1(C_187) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_185))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1071])).
% 7.97/2.87  tff(c_1184, plain, (![A_200, C_201]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_200), k2_struct_0('#skF_2'), C_201), '#skF_2', A_200) | ~v3_tops_2(C_201, A_200, '#skF_2') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_200), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_201, u1_struct_0(A_200), k2_struct_0('#skF_2')) | ~v1_funct_1(C_201) | ~l1_pre_topc(A_200))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_67, c_1082])).
% 7.97/2.87  tff(c_1189, plain, (![C_201]: (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_201), '#skF_2', '#skF_1') | ~v3_tops_2(C_201, '#skF_1', '#skF_2') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_201, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_201) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1184])).
% 7.97/2.87  tff(c_1197, plain, (![C_202]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_202), '#skF_2', '#skF_1') | ~v3_tops_2(C_202, '#skF_1', '#skF_2') | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_202, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_202))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_68, c_1189])).
% 7.97/2.87  tff(c_1204, plain, (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1197])).
% 7.97/2.87  tff(c_1208, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_40, c_640, c_1204])).
% 7.97/2.87  tff(c_18, plain, (![A_12, B_13, C_14]: (k2_tops_2(A_12, B_13, C_14)=k2_funct_1(C_14) | ~v2_funct_1(C_14) | k2_relset_1(A_12, B_13, C_14)!=B_13 | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_funct_2(C_14, A_12, B_13) | ~v1_funct_1(C_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.97/2.87  tff(c_1862, plain, (![B_269, A_270, C_271]: (k2_tops_2(B_269, A_270, k2_funct_1(C_271))=k2_funct_1(k2_funct_1(C_271)) | ~v2_funct_1(k2_funct_1(C_271)) | k2_relset_1(B_269, A_270, k2_funct_1(C_271))!=A_270 | ~v1_funct_2(k2_funct_1(C_271), B_269, A_270) | ~v1_funct_1(k2_funct_1(C_271)) | k2_relset_1(A_270, B_269, C_271)!=B_269 | ~v2_funct_1(C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_270, B_269))) | ~v1_funct_2(C_271, A_270, B_269) | ~v1_funct_1(C_271))), inference(resolution, [status(thm)], [c_646, c_18])).
% 7.97/2.87  tff(c_1868, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1862])).
% 7.97/2.87  tff(c_1872, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_246, c_620, c_619, c_633, c_1695, c_1476, c_1868])).
% 7.97/2.87  tff(c_3230, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_3200])).
% 7.97/2.87  tff(c_3074, plain, (![A_362, B_363, C_364]: (k2_tops_2(A_362, B_363, k2_funct_1(k2_funct_1(C_364)))=k2_funct_1(k2_funct_1(k2_funct_1(C_364))) | ~v2_funct_1(k2_funct_1(k2_funct_1(C_364))) | k2_relset_1(A_362, B_363, k2_funct_1(k2_funct_1(C_364)))!=B_363 | ~v1_funct_2(k2_funct_1(k2_funct_1(C_364)), A_362, B_363) | ~v1_funct_1(k2_funct_1(k2_funct_1(C_364))) | k2_relset_1(B_363, A_362, k2_funct_1(C_364))!=A_362 | ~v2_funct_1(k2_funct_1(C_364)) | ~v1_funct_2(k2_funct_1(C_364), B_363, A_362) | ~v1_funct_1(k2_funct_1(C_364)) | k2_relset_1(A_362, B_363, C_364)!=B_363 | ~v2_funct_1(C_364) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(A_362, B_363))) | ~v1_funct_2(C_364, A_362, B_363) | ~v1_funct_1(C_364))), inference(resolution, [status(thm)], [c_8, c_1862])).
% 7.97/2.87  tff(c_3532, plain, (![A_416, B_417, C_418]: (k2_tops_2(A_416, B_417, k2_funct_1(k2_funct_1(C_418)))=k2_funct_1(k2_funct_1(k2_funct_1(C_418))) | ~v2_funct_1(k2_funct_1(k2_funct_1(C_418))) | k2_relset_1(A_416, B_417, k2_funct_1(k2_funct_1(C_418)))!=B_417 | ~v1_funct_1(k2_funct_1(k2_funct_1(C_418))) | k2_relset_1(B_417, A_416, k2_funct_1(C_418))!=A_416 | ~v2_funct_1(k2_funct_1(C_418)) | ~v1_funct_2(k2_funct_1(C_418), B_417, A_416) | ~v1_funct_1(k2_funct_1(C_418)) | k2_relset_1(A_416, B_417, C_418)!=B_417 | ~v2_funct_1(C_418) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_416, B_417))) | ~v1_funct_2(C_418, A_416, B_417) | ~v1_funct_1(C_418))), inference(resolution, [status(thm)], [c_663, c_3074])).
% 7.97/2.87  tff(c_3541, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3532])).
% 7.97/2.87  tff(c_3546, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_246, c_620, c_619, c_633, c_1476, c_1695, c_1694, c_3244, c_3230, c_3541])).
% 7.97/2.87  tff(c_3560, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_3546])).
% 7.97/2.87  tff(c_3570, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_46, c_246, c_640, c_3560])).
% 7.97/2.87  tff(c_3656, plain, (![B_8, A_7]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_8, A_7))) | k2_relset_1(A_7, B_8, k2_funct_1(k2_funct_1('#skF_3')))!=B_8 | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_7, B_8) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_3570, c_8])).
% 7.97/2.87  tff(c_4603, plain, (![B_425, A_426]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_425, A_426))) | k2_relset_1(A_426, B_425, k2_funct_1(k2_funct_1('#skF_3')))!=B_425 | ~m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_426, B_425))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_426, B_425))), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_3230, c_3656])).
% 7.97/2.87  tff(c_4617, plain, (![B_425, A_426]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_425, A_426))) | k2_relset_1(A_426, B_425, k2_funct_1(k2_funct_1('#skF_3')))!=B_425 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_426, B_425))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_426, B_425) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_4603])).
% 7.97/2.87  tff(c_4627, plain, (![B_427, A_428]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_427, A_428))) | k2_relset_1(A_428, B_427, k2_funct_1(k2_funct_1('#skF_3')))!=B_427 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_428, B_427))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_428, B_427))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_46, c_246, c_4617])).
% 7.97/2.87  tff(c_1696, plain, (![C_252, A_253, B_254]: (v3_tops_2(C_252, A_253, B_254) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_253), u1_struct_0(B_254), C_252), B_254, A_253) | ~v5_pre_topc(C_252, A_253, B_254) | ~v2_funct_1(C_252) | k2_relset_1(u1_struct_0(A_253), u1_struct_0(B_254), C_252)!=k2_struct_0(B_254) | k1_relset_1(u1_struct_0(A_253), u1_struct_0(B_254), C_252)!=k2_struct_0(A_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_253), u1_struct_0(B_254)))) | ~v1_funct_2(C_252, u1_struct_0(A_253), u1_struct_0(B_254)) | ~v1_funct_1(C_252) | ~l1_pre_topc(B_254) | ~l1_pre_topc(A_253))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.97/2.87  tff(c_1700, plain, (![C_252, A_253]: (v3_tops_2(C_252, A_253, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_253), k2_struct_0('#skF_1'), C_252), '#skF_1', A_253) | ~v5_pre_topc(C_252, A_253, '#skF_1') | ~v2_funct_1(C_252) | k2_relset_1(u1_struct_0(A_253), u1_struct_0('#skF_1'), C_252)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_253), u1_struct_0('#skF_1'), C_252)!=k2_struct_0(A_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_253), u1_struct_0('#skF_1')))) | ~v1_funct_2(C_252, u1_struct_0(A_253), u1_struct_0('#skF_1')) | ~v1_funct_1(C_252) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_253))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1696])).
% 7.97/2.87  tff(c_3065, plain, (![C_360, A_361]: (v3_tops_2(C_360, A_361, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_361), k2_struct_0('#skF_1'), C_360), '#skF_1', A_361) | ~v5_pre_topc(C_360, A_361, '#skF_1') | ~v2_funct_1(C_360) | k2_relset_1(u1_struct_0(A_361), k2_struct_0('#skF_1'), C_360)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_361), k2_struct_0('#skF_1'), C_360)!=k2_struct_0(A_361) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_360, u1_struct_0(A_361), k2_struct_0('#skF_1')) | ~v1_funct_1(C_360) | ~l1_pre_topc(A_361))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_68, c_68, c_68, c_1700])).
% 7.97/2.87  tff(c_3069, plain, (![C_360]: (v3_tops_2(C_360, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_360), '#skF_1', '#skF_2') | ~v5_pre_topc(C_360, '#skF_2', '#skF_1') | ~v2_funct_1(C_360) | k2_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_360)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_360)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_360, u1_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_360) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_3065])).
% 7.97/2.87  tff(c_3073, plain, (![C_360]: (v3_tops_2(C_360, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_360), '#skF_1', '#skF_2') | ~v5_pre_topc(C_360, '#skF_2', '#skF_1') | ~v2_funct_1(C_360) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_360)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_360)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_360, k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_360))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_67, c_67, c_67, c_3069])).
% 7.97/2.87  tff(c_4677, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4627, c_3073])).
% 7.97/2.87  tff(c_5115, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3244, c_619, c_633, c_1561, c_1695, c_1476, c_1208, c_1872, c_4677])).
% 7.97/2.87  tff(c_5116, plain, (~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_641, c_5115])).
% 7.97/2.87  tff(c_5468, plain, (~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_5116])).
% 7.97/2.87  tff(c_5471, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_663, c_5468])).
% 7.97/2.87  tff(c_5478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_82, c_246, c_620, c_619, c_633, c_1476, c_1695, c_5471])).
% 7.97/2.87  tff(c_5479, plain, (~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_5116])).
% 7.97/2.87  tff(c_5483, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_5479])).
% 7.97/2.87  tff(c_5486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_46, c_246, c_878, c_5483])).
% 7.97/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.87  
% 7.97/2.87  Inference rules
% 7.97/2.87  ----------------------
% 7.97/2.87  #Ref     : 0
% 7.97/2.87  #Sup     : 997
% 7.97/2.87  #Fact    : 0
% 7.97/2.87  #Define  : 0
% 7.97/2.87  #Split   : 10
% 7.97/2.87  #Chain   : 0
% 7.97/2.87  #Close   : 0
% 7.97/2.87  
% 7.97/2.87  Ordering : KBO
% 7.97/2.87  
% 7.97/2.87  Simplification rules
% 7.97/2.87  ----------------------
% 7.97/2.87  #Subsume      : 155
% 7.97/2.87  #Demod        : 2743
% 7.97/2.87  #Tautology    : 211
% 7.97/2.87  #SimpNegUnit  : 18
% 7.97/2.87  #BackRed      : 5
% 7.97/2.87  
% 7.97/2.87  #Partial instantiations: 0
% 7.97/2.87  #Strategies tried      : 1
% 7.97/2.87  
% 7.97/2.87  Timing (in seconds)
% 7.97/2.87  ----------------------
% 7.97/2.87  Preprocessing        : 0.37
% 7.97/2.87  Parsing              : 0.20
% 7.97/2.87  CNF conversion       : 0.03
% 7.97/2.87  Main loop            : 1.66
% 7.97/2.87  Inferencing          : 0.48
% 7.97/2.87  Reduction            : 0.63
% 7.97/2.87  Demodulation         : 0.47
% 7.97/2.87  BG Simplification    : 0.07
% 7.97/2.87  Subsumption          : 0.40
% 7.97/2.87  Abstraction          : 0.09
% 7.97/2.87  MUC search           : 0.00
% 7.97/2.87  Cooper               : 0.00
% 7.97/2.87  Total                : 2.12
% 7.97/2.87  Index Insertion      : 0.00
% 7.97/2.88  Index Deletion       : 0.00
% 7.97/2.88  Index Matching       : 0.00
% 7.97/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
