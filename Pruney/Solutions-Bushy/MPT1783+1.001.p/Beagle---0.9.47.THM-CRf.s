%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1783+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:23 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 154 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 659 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k4_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k3_struct_0,type,(
    k3_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( v1_funct_1(k4_tmap_1(A,B))
              & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
              & v5_pre_topc(k4_tmap_1(A,B),B,A)
              & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_tmap_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & v5_pre_topc(k3_struct_0(A),A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_tmap_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_36,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => k4_tmap_1(A,B) = k2_tmap_1(A,A,k3_struct_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k3_struct_0(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_struct_0)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & v5_pre_topc(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_28,plain,(
    ! [A_12] :
      ( v1_funct_1(k3_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_24,plain,(
    ! [A_12] :
      ( v5_pre_topc(k3_struct_0(A_12),A_12,A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k2_tmap_1(A_1,A_1,k3_struct_0(A_1),B_3) = k4_tmap_1(A_1,B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [A_12] :
      ( v1_funct_2(k3_struct_0(A_12),u1_struct_0(A_12),u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4,plain,(
    ! [A_4] :
      ( m1_subset_1(k3_struct_0(A_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4),u1_struct_0(A_4))))
      | ~ l1_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( v5_pre_topc(k2_tmap_1(A_47,B_48,C_49,D_50),D_50,B_48)
      | ~ m1_pre_topc(D_50,A_47)
      | v2_struct_0(D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(B_48))))
      | ~ v5_pre_topc(C_49,A_47,B_48)
      | ~ v1_funct_2(C_49,u1_struct_0(A_47),u1_struct_0(B_48))
      | ~ v1_funct_1(C_49)
      | ~ l1_pre_topc(B_48)
      | ~ v2_pre_topc(B_48)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_145,plain,(
    ! [A_53,D_54] :
      ( v5_pre_topc(k2_tmap_1(A_53,A_53,k3_struct_0(A_53),D_54),D_54,A_53)
      | ~ m1_pre_topc(D_54,A_53)
      | v2_struct_0(D_54)
      | ~ v5_pre_topc(k3_struct_0(A_53),A_53,A_53)
      | ~ v1_funct_2(k3_struct_0(A_53),u1_struct_0(A_53),u1_struct_0(A_53))
      | ~ v1_funct_1(k3_struct_0(A_53))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_165,plain,(
    ! [A_59,D_60] :
      ( v5_pre_topc(k2_tmap_1(A_59,A_59,k3_struct_0(A_59),D_60),D_60,A_59)
      | ~ m1_pre_topc(D_60,A_59)
      | v2_struct_0(D_60)
      | ~ v5_pre_topc(k3_struct_0(A_59),A_59,A_59)
      | ~ v1_funct_1(k3_struct_0(A_59))
      | ~ l1_struct_0(A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_26,c_145])).

tff(c_169,plain,(
    ! [A_61,B_62] :
      ( v5_pre_topc(k4_tmap_1(A_61,B_62),B_62,A_61)
      | ~ m1_pre_topc(B_62,A_61)
      | v2_struct_0(B_62)
      | ~ v5_pre_topc(k3_struct_0(A_61),A_61,A_61)
      | ~ v1_funct_1(k3_struct_0(A_61))
      | ~ l1_struct_0(A_61)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61)
      | ~ m1_pre_topc(B_62,A_61)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_173,plain,(
    ! [A_63,B_64] :
      ( v5_pre_topc(k4_tmap_1(A_63,B_64),B_64,A_63)
      | v2_struct_0(B_64)
      | ~ v1_funct_1(k3_struct_0(A_63))
      | ~ l1_struct_0(A_63)
      | ~ m1_pre_topc(B_64,A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_24,c_169])).

tff(c_86,plain,(
    ! [A_33,B_34] :
      ( v1_funct_2(k4_tmap_1(A_33,B_34),u1_struct_0(B_34),u1_struct_0(A_33))
      | ~ m1_pre_topc(B_34,A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k4_tmap_1(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_32),u1_struct_0(A_31))))
      | ~ m1_pre_topc(B_32,A_31)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [A_20,B_21] :
      ( v1_funct_1(k4_tmap_1(A_20,B_21))
      | ~ m1_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,
    ( ~ m1_subset_1(k4_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
    | ~ v5_pre_topc(k4_tmap_1('#skF_1','#skF_2'),'#skF_2','#skF_1')
    | ~ v1_funct_2(k4_tmap_1('#skF_1','#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1(k4_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_45,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_51,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_45])).

tff(c_54,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_51])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_54])).

tff(c_57,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_1','#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v5_pre_topc(k4_tmap_1('#skF_1','#skF_2'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k4_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_63,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_77,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_63])).

tff(c_80,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_77])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_80])).

tff(c_83,plain,
    ( ~ v5_pre_topc(k4_tmap_1('#skF_1','#skF_2'),'#skF_2','#skF_1')
    | ~ v1_funct_2(k4_tmap_1('#skF_1','#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_85,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_1','#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_89,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_85])).

tff(c_92,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_89])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_92])).

tff(c_95,plain,(
    ~ v5_pre_topc(k4_tmap_1('#skF_1','#skF_2'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_176,plain,
    ( v2_struct_0('#skF_2')
    | ~ v1_funct_1(k3_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_173,c_95])).

tff(c_179,plain,
    ( v2_struct_0('#skF_2')
    | ~ v1_funct_1(k3_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_176])).

tff(c_180,plain,
    ( ~ v1_funct_1(k3_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_179])).

tff(c_181,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_188,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_181])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_188])).

tff(c_193,plain,(
    ~ v1_funct_1(k3_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_197,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_193])).

tff(c_203,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_197])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_203])).

%------------------------------------------------------------------------------
