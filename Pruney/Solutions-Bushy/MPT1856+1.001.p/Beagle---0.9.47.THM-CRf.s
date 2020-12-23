%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1856+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:33 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 328 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v2_pre_topc(k1_tex_2(A,B))
             => ( v1_tdlat_3(k1_tex_2(A,B))
                & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & ~ v1_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tex_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & ~ v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_tex_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_98,plain,(
    ! [A_25,B_26] :
      ( ~ v2_struct_0(k1_tex_2(A_25,B_26))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_101,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_104,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_105,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_104])).

tff(c_41,plain,(
    ! [A_15,B_16] :
      ( ~ v2_struct_0(k1_tex_2(A_15,B_16))
      | ~ m1_subset_1(B_16,u1_struct_0(A_15))
      | ~ l1_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_47,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_48,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_47])).

tff(c_28,plain,
    ( ~ v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    v2_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_57,plain,(
    ! [A_19,B_20] :
      ( v7_struct_0(k1_tex_2(A_19,B_20))
      | ~ m1_subset_1(B_20,u1_struct_0(A_19))
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_63,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_60])).

tff(c_64,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( ~ v7_struct_0(A_1)
      | v1_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_73,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_67])).

tff(c_74,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_73])).

tff(c_79,plain,(
    ! [A_21,B_22] :
      ( m1_pre_topc(k1_tex_2(A_21,B_22),A_21)
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_81,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_84,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81])).

tff(c_85,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_84])).

tff(c_20,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_88,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_20])).

tff(c_91,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_88])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_91])).

tff(c_94,plain,(
    ~ v2_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_114,plain,(
    ! [A_29,B_30] :
      ( v7_struct_0(k1_tex_2(A_29,B_30))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_117,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_114])).

tff(c_120,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_117])).

tff(c_121,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_120])).

tff(c_10,plain,(
    ! [A_2] :
      ( ~ v7_struct_0(A_2)
      | v2_tdlat_3(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_124,plain,
    ( v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_121,c_10])).

tff(c_130,plain,
    ( v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_124])).

tff(c_131,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_94,c_130])).

tff(c_136,plain,(
    ! [A_31,B_32] :
      ( m1_pre_topc(k1_tex_2(A_31,B_32),A_31)
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_138,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_136])).

tff(c_141,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_138])).

tff(c_142,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_141])).

tff(c_145,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_20])).

tff(c_148,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_145])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_148])).

%------------------------------------------------------------------------------
