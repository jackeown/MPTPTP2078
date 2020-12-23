%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:07 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 387 expanded)
%              Number of leaves         :   25 ( 147 expanded)
%              Depth                    :   14
%              Number of atoms          :  194 (1152 expanded)
%              Number of equality atoms :   11 (  38 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_64,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_92,axiom,(
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

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_123,plain,(
    ! [A_41,B_42] :
      ( ~ v2_struct_0(k1_tex_2(A_41,B_42))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_126,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_123])).

tff(c_129,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_126])).

tff(c_130,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_129])).

tff(c_131,plain,(
    ! [A_43,B_44] :
      ( v1_pre_topc(k1_tex_2(A_43,B_44))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_134,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_137,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_134])).

tff(c_138,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_137])).

tff(c_139,plain,(
    ! [A_45,B_46] :
      ( m1_pre_topc(k1_tex_2(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_141,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_139])).

tff(c_144,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_141])).

tff(c_145,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_144])).

tff(c_149,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(u1_struct_0(A_54),B_55) = u1_struct_0(k1_tex_2(A_54,B_55))
      | ~ m1_pre_topc(k1_tex_2(A_54,B_55),A_54)
      | ~ v1_pre_topc(k1_tex_2(A_54,B_55))
      | v2_struct_0(k1_tex_2(A_54,B_55))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_151,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_145,c_149])).

tff(c_154,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_138,c_151])).

tff(c_155,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_130,c_154])).

tff(c_34,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_57,plain,(
    ! [A_30,B_31] :
      ( m1_pre_topc(k1_tex_2(A_30,B_31),A_30)
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_62,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_59])).

tff(c_63,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_62])).

tff(c_39,plain,(
    ! [A_26,B_27] :
      ( ~ v2_struct_0(k1_tex_2(A_26,B_27))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_39])).

tff(c_45,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42])).

tff(c_46,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_45])).

tff(c_49,plain,(
    ! [A_28,B_29] :
      ( v1_pre_topc(k1_tex_2(A_28,B_29))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_55,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52])).

tff(c_56,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_55])).

tff(c_67,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(u1_struct_0(A_39),B_40) = u1_struct_0(k1_tex_2(A_39,B_40))
      | ~ m1_pre_topc(k1_tex_2(A_39,B_40),A_39)
      | ~ v1_pre_topc(k1_tex_2(A_39,B_40))
      | v2_struct_0(k1_tex_2(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_67])).

tff(c_72,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_56,c_69])).

tff(c_73,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_46,c_72])).

tff(c_74,plain,(
    v1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_38])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k6_domain_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_6])).

tff(c_87,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_80])).

tff(c_89,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_4])).

tff(c_95,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_92])).

tff(c_98,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_98])).

tff(c_103,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_20,plain,(
    ! [B_18,A_14] :
      ( v1_tex_2(B_18,A_14)
      | ~ v1_subset_1(u1_struct_0(B_18),u1_struct_0(A_14))
      | ~ m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_pre_topc(B_18,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_110,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),u1_struct_0('#skF_1'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_103,c_20])).

tff(c_116,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_63,c_74,c_110])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_116])).

tff(c_120,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_156,plain,(
    ~ v1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_120])).

tff(c_119,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_162,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_6])).

tff(c_169,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_162])).

tff(c_171,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_174,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_171,c_4])).

tff(c_177,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_174])).

tff(c_180,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_180])).

tff(c_185,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_18,plain,(
    ! [B_18,A_14] :
      ( v1_subset_1(u1_struct_0(B_18),u1_struct_0(A_14))
      | ~ v1_tex_2(B_18,A_14)
      | ~ m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_pre_topc(B_18,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_192,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_185,c_18])).

tff(c_198,plain,(
    v1_subset_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_145,c_119,c_192])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.30  
% 2.22/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.31  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.45/1.31  
% 2.45/1.31  %Foreground sorts:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Background operators:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Foreground operators:
% 2.45/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.31  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.45/1.31  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.45/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.45/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.45/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.31  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.45/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.31  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.45/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.31  
% 2.45/1.33  tff(f_105, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 2.45/1.33  tff(f_78, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.45/1.33  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 2.45/1.33  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.45/1.33  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.45/1.33  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.45/1.33  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 2.45/1.33  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.45/1.33  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.45/1.33  tff(c_22, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.45/1.33  tff(c_123, plain, (![A_41, B_42]: (~v2_struct_0(k1_tex_2(A_41, B_42)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.33  tff(c_126, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_123])).
% 2.45/1.33  tff(c_129, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_126])).
% 2.45/1.33  tff(c_130, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_129])).
% 2.45/1.33  tff(c_131, plain, (![A_43, B_44]: (v1_pre_topc(k1_tex_2(A_43, B_44)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.33  tff(c_134, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_131])).
% 2.45/1.33  tff(c_137, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_134])).
% 2.45/1.33  tff(c_138, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_137])).
% 2.45/1.33  tff(c_139, plain, (![A_45, B_46]: (m1_pre_topc(k1_tex_2(A_45, B_46), A_45) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.33  tff(c_141, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_139])).
% 2.45/1.33  tff(c_144, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_141])).
% 2.45/1.33  tff(c_145, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_26, c_144])).
% 2.45/1.33  tff(c_149, plain, (![A_54, B_55]: (k6_domain_1(u1_struct_0(A_54), B_55)=u1_struct_0(k1_tex_2(A_54, B_55)) | ~m1_pre_topc(k1_tex_2(A_54, B_55), A_54) | ~v1_pre_topc(k1_tex_2(A_54, B_55)) | v2_struct_0(k1_tex_2(A_54, B_55)) | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~l1_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.33  tff(c_151, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_145, c_149])).
% 2.45/1.33  tff(c_154, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_138, c_151])).
% 2.45/1.33  tff(c_155, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_130, c_154])).
% 2.45/1.33  tff(c_34, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.45/1.33  tff(c_38, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.45/1.33  tff(c_28, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.45/1.33  tff(c_48, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 2.45/1.33  tff(c_57, plain, (![A_30, B_31]: (m1_pre_topc(k1_tex_2(A_30, B_31), A_30) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.33  tff(c_59, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_57])).
% 2.45/1.33  tff(c_62, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_59])).
% 2.45/1.33  tff(c_63, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_26, c_62])).
% 2.45/1.33  tff(c_39, plain, (![A_26, B_27]: (~v2_struct_0(k1_tex_2(A_26, B_27)) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.33  tff(c_42, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_39])).
% 2.45/1.33  tff(c_45, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_42])).
% 2.45/1.33  tff(c_46, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_45])).
% 2.45/1.33  tff(c_49, plain, (![A_28, B_29]: (v1_pre_topc(k1_tex_2(A_28, B_29)) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.33  tff(c_52, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_49])).
% 2.45/1.33  tff(c_55, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52])).
% 2.45/1.33  tff(c_56, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_55])).
% 2.45/1.33  tff(c_67, plain, (![A_39, B_40]: (k6_domain_1(u1_struct_0(A_39), B_40)=u1_struct_0(k1_tex_2(A_39, B_40)) | ~m1_pre_topc(k1_tex_2(A_39, B_40), A_39) | ~v1_pre_topc(k1_tex_2(A_39, B_40)) | v2_struct_0(k1_tex_2(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.33  tff(c_69, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_63, c_67])).
% 2.45/1.33  tff(c_72, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_56, c_69])).
% 2.45/1.33  tff(c_73, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_46, c_72])).
% 2.45/1.33  tff(c_74, plain, (v1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_38])).
% 2.45/1.33  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.33  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k6_domain_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.45/1.33  tff(c_80, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_6])).
% 2.45/1.33  tff(c_87, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_80])).
% 2.45/1.33  tff(c_89, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_87])).
% 2.45/1.33  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.33  tff(c_92, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_89, c_4])).
% 2.45/1.33  tff(c_95, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_26, c_92])).
% 2.45/1.33  tff(c_98, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_95])).
% 2.45/1.33  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_98])).
% 2.45/1.33  tff(c_103, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_87])).
% 2.45/1.33  tff(c_20, plain, (![B_18, A_14]: (v1_tex_2(B_18, A_14) | ~v1_subset_1(u1_struct_0(B_18), u1_struct_0(A_14)) | ~m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_pre_topc(B_18, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.45/1.33  tff(c_110, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~v1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), u1_struct_0('#skF_1')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_103, c_20])).
% 2.45/1.33  tff(c_116, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_63, c_74, c_110])).
% 2.45/1.33  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_116])).
% 2.45/1.33  tff(c_120, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 2.45/1.33  tff(c_156, plain, (~v1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_120])).
% 2.45/1.33  tff(c_119, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.45/1.33  tff(c_162, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_6])).
% 2.45/1.33  tff(c_169, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_162])).
% 2.45/1.33  tff(c_171, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_169])).
% 2.45/1.33  tff(c_174, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_171, c_4])).
% 2.45/1.33  tff(c_177, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_26, c_174])).
% 2.45/1.33  tff(c_180, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_177])).
% 2.45/1.33  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_180])).
% 2.45/1.33  tff(c_185, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_169])).
% 2.45/1.33  tff(c_18, plain, (![B_18, A_14]: (v1_subset_1(u1_struct_0(B_18), u1_struct_0(A_14)) | ~v1_tex_2(B_18, A_14) | ~m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_pre_topc(B_18, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.45/1.33  tff(c_192, plain, (v1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_185, c_18])).
% 2.45/1.33  tff(c_198, plain, (v1_subset_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_145, c_119, c_192])).
% 2.45/1.33  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_198])).
% 2.45/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  Inference rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Ref     : 0
% 2.45/1.33  #Sup     : 24
% 2.45/1.33  #Fact    : 0
% 2.45/1.33  #Define  : 0
% 2.45/1.33  #Split   : 3
% 2.45/1.33  #Chain   : 0
% 2.45/1.33  #Close   : 0
% 2.45/1.33  
% 2.45/1.33  Ordering : KBO
% 2.45/1.33  
% 2.45/1.33  Simplification rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Subsume      : 3
% 2.45/1.33  #Demod        : 36
% 2.45/1.33  #Tautology    : 6
% 2.45/1.33  #SimpNegUnit  : 14
% 2.45/1.33  #BackRed      : 2
% 2.45/1.33  
% 2.45/1.33  #Partial instantiations: 0
% 2.45/1.33  #Strategies tried      : 1
% 2.45/1.33  
% 2.45/1.33  Timing (in seconds)
% 2.45/1.33  ----------------------
% 2.45/1.33  Preprocessing        : 0.34
% 2.45/1.33  Parsing              : 0.18
% 2.45/1.33  CNF conversion       : 0.02
% 2.45/1.33  Main loop            : 0.20
% 2.45/1.33  Inferencing          : 0.08
% 2.45/1.33  Reduction            : 0.06
% 2.45/1.33  Demodulation         : 0.04
% 2.45/1.33  BG Simplification    : 0.01
% 2.45/1.33  Subsumption          : 0.03
% 2.45/1.33  Abstraction          : 0.01
% 2.45/1.33  MUC search           : 0.00
% 2.45/1.33  Cooper               : 0.00
% 2.45/1.33  Total                : 0.58
% 2.45/1.33  Index Insertion      : 0.00
% 2.45/1.33  Index Deletion       : 0.00
% 2.45/1.33  Index Matching       : 0.00
% 2.45/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
