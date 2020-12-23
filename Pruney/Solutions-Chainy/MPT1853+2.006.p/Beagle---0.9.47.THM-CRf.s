%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:00 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 175 expanded)
%              Number of leaves         :   29 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  185 ( 454 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

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

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc13_tex_2)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_173,plain,(
    ! [A_46,B_47] :
      ( ~ v2_struct_0(k1_tex_2(A_46,B_47))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_176,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_173])).

tff(c_179,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_176])).

tff(c_180,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_179])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_40,B_41] :
      ( v1_subset_1(k6_domain_1(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,A_40)
      | v1_zfmisc_1(A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_60,plain,(
    ! [A_28,B_29] :
      ( ~ v2_struct_0(k1_tex_2(A_28,B_29))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_63,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_66,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63])).

tff(c_67,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_66])).

tff(c_76,plain,(
    ! [A_32,B_33] :
      ( m1_pre_topc(k1_tex_2(A_32,B_33),A_32)
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_81,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_78])).

tff(c_82,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_81])).

tff(c_52,plain,(
    ! [A_26,B_27] :
      ( v7_struct_0(k1_tex_2(A_26,B_27))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_55,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_58,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_55])).

tff(c_59,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_58])).

tff(c_84,plain,(
    ! [B_36,A_37] :
      ( ~ v7_struct_0(B_36)
      | v1_tex_2(B_36,A_37)
      | v2_struct_0(B_36)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37)
      | v7_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_48,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_51,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_90,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_51])).

tff(c_94,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82,c_59,c_90])).

tff(c_95,plain,(
    v7_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_67,c_94])).

tff(c_96,plain,(
    ! [A_38,B_39] :
      ( ~ v7_struct_0(A_38)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_38),B_39),u1_struct_0(A_38))
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_103,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_107,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_95,c_103])).

tff(c_108,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_107])).

tff(c_111,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_108])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_111])).

tff(c_117,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_121,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_118,c_117])).

tff(c_124,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_121])).

tff(c_125,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_125,c_4])).

tff(c_131,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_128])).

tff(c_134,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_134])).

tff(c_139,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v7_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_146,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_139,c_6])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_150,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_150])).

tff(c_155,plain,(
    v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_181,plain,(
    ! [A_48,B_49] :
      ( m1_pre_topc(k1_tex_2(A_48,B_49),A_48)
      | ~ m1_subset_1(B_49,u1_struct_0(A_48))
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_183,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_181])).

tff(c_186,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_183])).

tff(c_187,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_186])).

tff(c_116,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_188,plain,(
    ! [B_50,A_51] :
      ( ~ v1_tex_2(B_50,A_51)
      | v2_struct_0(B_50)
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v7_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_191,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_116,c_188])).

tff(c_194,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_34,c_187,c_191])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_180,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.23  
% 2.12/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.23  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 2.17/1.23  
% 2.17/1.23  %Foreground sorts:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Background operators:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Foreground operators:
% 2.17/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.17/1.23  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.17/1.23  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.17/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.17/1.23  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.17/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.23  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.17/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.23  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.23  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.17/1.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.17/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.23  
% 2.17/1.25  tff(f_152, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 2.17/1.25  tff(f_115, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.17/1.25  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.17/1.25  tff(f_126, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 2.17/1.25  tff(f_101, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.17/1.25  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.17/1.25  tff(f_139, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 2.17/1.25  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.17/1.25  tff(f_45, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.17/1.25  tff(f_64, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.17/1.25  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.17/1.25  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.17/1.25  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.17/1.25  tff(c_173, plain, (![A_46, B_47]: (~v2_struct_0(k1_tex_2(A_46, B_47)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.17/1.25  tff(c_176, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_173])).
% 2.17/1.25  tff(c_179, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_176])).
% 2.17/1.25  tff(c_180, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_179])).
% 2.17/1.25  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.25  tff(c_118, plain, (![A_40, B_41]: (v1_subset_1(k6_domain_1(A_40, B_41), A_40) | ~m1_subset_1(B_41, A_40) | v1_zfmisc_1(A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.17/1.25  tff(c_60, plain, (![A_28, B_29]: (~v2_struct_0(k1_tex_2(A_28, B_29)) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.17/1.25  tff(c_63, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_60])).
% 2.17/1.25  tff(c_66, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_63])).
% 2.17/1.25  tff(c_67, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_66])).
% 2.17/1.25  tff(c_76, plain, (![A_32, B_33]: (m1_pre_topc(k1_tex_2(A_32, B_33), A_32) | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_78, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_76])).
% 2.17/1.25  tff(c_81, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_78])).
% 2.17/1.25  tff(c_82, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_81])).
% 2.17/1.25  tff(c_52, plain, (![A_26, B_27]: (v7_struct_0(k1_tex_2(A_26, B_27)) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.17/1.25  tff(c_55, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_52])).
% 2.17/1.25  tff(c_58, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_55])).
% 2.17/1.25  tff(c_59, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_58])).
% 2.17/1.25  tff(c_84, plain, (![B_36, A_37]: (~v7_struct_0(B_36) | v1_tex_2(B_36, A_37) | v2_struct_0(B_36) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37) | v7_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.25  tff(c_44, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.17/1.25  tff(c_48, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.17/1.25  tff(c_38, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.17/1.25  tff(c_51, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 2.17/1.25  tff(c_90, plain, (~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_51])).
% 2.17/1.25  tff(c_94, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_82, c_59, c_90])).
% 2.17/1.25  tff(c_95, plain, (v7_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_67, c_94])).
% 2.17/1.25  tff(c_96, plain, (![A_38, B_39]: (~v7_struct_0(A_38) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_38), B_39), u1_struct_0(A_38)) | ~m1_subset_1(B_39, u1_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.17/1.25  tff(c_103, plain, (~v7_struct_0('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_96])).
% 2.17/1.25  tff(c_107, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_95, c_103])).
% 2.17/1.25  tff(c_108, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_107])).
% 2.17/1.25  tff(c_111, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_108])).
% 2.17/1.25  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_111])).
% 2.17/1.25  tff(c_117, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_44])).
% 2.17/1.25  tff(c_121, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_118, c_117])).
% 2.17/1.25  tff(c_124, plain, (v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_121])).
% 2.17/1.25  tff(c_125, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_124])).
% 2.17/1.25  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.25  tff(c_128, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_125, c_4])).
% 2.17/1.25  tff(c_131, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_128])).
% 2.17/1.25  tff(c_134, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_131])).
% 2.17/1.25  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_134])).
% 2.17/1.25  tff(c_139, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_124])).
% 2.17/1.25  tff(c_6, plain, (![A_3]: (~v1_zfmisc_1(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v7_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.25  tff(c_146, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_139, c_6])).
% 2.17/1.25  tff(c_147, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_146])).
% 2.17/1.25  tff(c_150, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_147])).
% 2.17/1.25  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_150])).
% 2.17/1.25  tff(c_155, plain, (v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_146])).
% 2.17/1.25  tff(c_181, plain, (![A_48, B_49]: (m1_pre_topc(k1_tex_2(A_48, B_49), A_48) | ~m1_subset_1(B_49, u1_struct_0(A_48)) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_183, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_181])).
% 2.17/1.25  tff(c_186, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_183])).
% 2.17/1.25  tff(c_187, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_186])).
% 2.17/1.25  tff(c_116, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 2.17/1.25  tff(c_188, plain, (![B_50, A_51]: (~v1_tex_2(B_50, A_51) | v2_struct_0(B_50) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51) | ~v7_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.25  tff(c_191, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_116, c_188])).
% 2.17/1.25  tff(c_194, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_34, c_187, c_191])).
% 2.17/1.25  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_180, c_194])).
% 2.17/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  Inference rules
% 2.17/1.25  ----------------------
% 2.17/1.25  #Ref     : 0
% 2.17/1.25  #Sup     : 19
% 2.17/1.25  #Fact    : 0
% 2.17/1.25  #Define  : 0
% 2.17/1.25  #Split   : 3
% 2.17/1.25  #Chain   : 0
% 2.17/1.25  #Close   : 0
% 2.17/1.25  
% 2.17/1.25  Ordering : KBO
% 2.17/1.25  
% 2.17/1.25  Simplification rules
% 2.17/1.25  ----------------------
% 2.17/1.25  #Subsume      : 3
% 2.17/1.25  #Demod        : 22
% 2.17/1.25  #Tautology    : 5
% 2.17/1.25  #SimpNegUnit  : 12
% 2.17/1.25  #BackRed      : 0
% 2.17/1.25  
% 2.17/1.25  #Partial instantiations: 0
% 2.17/1.25  #Strategies tried      : 1
% 2.17/1.25  
% 2.17/1.25  Timing (in seconds)
% 2.17/1.25  ----------------------
% 2.17/1.25  Preprocessing        : 0.31
% 2.17/1.25  Parsing              : 0.18
% 2.17/1.25  CNF conversion       : 0.02
% 2.17/1.25  Main loop            : 0.17
% 2.17/1.25  Inferencing          : 0.07
% 2.17/1.25  Reduction            : 0.05
% 2.17/1.25  Demodulation         : 0.03
% 2.17/1.25  BG Simplification    : 0.01
% 2.17/1.25  Subsumption          : 0.02
% 2.17/1.25  Abstraction          : 0.01
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.17/1.25  Total                : 0.52
% 2.17/1.25  Index Insertion      : 0.00
% 2.17/1.25  Index Deletion       : 0.00
% 2.17/1.25  Index Matching       : 0.00
% 2.17/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
