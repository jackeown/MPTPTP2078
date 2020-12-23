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
% DateTime   : Thu Dec  3 10:27:57 EST 2020

% Result     : Theorem 18.09s
% Output     : CNFRefutation 18.18s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 217 expanded)
%              Number of leaves         :   24 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  322 ( 969 expanded)
%              Number of equality atoms :   61 ( 209 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( C = u1_struct_0(B)
                   => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_22,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20,plain,(
    ! [B_30,A_28] :
      ( m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_39,plain,(
    ! [A_37,B_38] :
      ( l1_pre_topc(k6_tmap_1(A_37,B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_43,plain,(
    ! [A_28,B_30] :
      ( l1_pre_topc(k6_tmap_1(A_28,u1_struct_0(B_30)))
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_20,c_39])).

tff(c_51,plain,(
    ! [A_45,B_46] :
      ( v1_pre_topc(k6_tmap_1(A_45,B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_55,plain,(
    ! [A_28,B_30] :
      ( v1_pre_topc(k6_tmap_1(A_28,u1_struct_0(B_30)))
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_45,plain,(
    ! [A_41,B_42] :
      ( v2_pre_topc(k6_tmap_1(A_41,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49,plain,(
    ! [A_28,B_30] :
      ( v2_pre_topc(k6_tmap_1(A_28,u1_struct_0(B_30)))
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_20,c_45])).

tff(c_112,plain,(
    ! [B_55,A_56,C_57] :
      ( u1_struct_0(B_55) = '#skF_1'(A_56,B_55,C_57)
      | k8_tmap_1(A_56,B_55) = C_57
      | ~ l1_pre_topc(C_57)
      | ~ v2_pre_topc(C_57)
      | ~ v1_pre_topc(C_57)
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_523,plain,(
    ! [A_172,B_173,A_174,B_175] :
      ( '#skF_1'(A_172,B_173,k6_tmap_1(A_174,u1_struct_0(B_175))) = u1_struct_0(B_173)
      | k8_tmap_1(A_172,B_173) = k6_tmap_1(A_174,u1_struct_0(B_175))
      | ~ l1_pre_topc(k6_tmap_1(A_174,u1_struct_0(B_175)))
      | ~ v1_pre_topc(k6_tmap_1(A_174,u1_struct_0(B_175)))
      | ~ m1_pre_topc(B_173,A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174)
      | ~ m1_pre_topc(B_175,A_174)
      | ~ l1_pre_topc(A_174) ) ),
    inference(resolution,[status(thm)],[c_49,c_112])).

tff(c_544,plain,(
    ! [A_180,B_181,A_182,B_183] :
      ( '#skF_1'(A_180,B_181,k6_tmap_1(A_182,u1_struct_0(B_183))) = u1_struct_0(B_181)
      | k8_tmap_1(A_180,B_181) = k6_tmap_1(A_182,u1_struct_0(B_183))
      | ~ l1_pre_topc(k6_tmap_1(A_182,u1_struct_0(B_183)))
      | ~ m1_pre_topc(B_181,A_180)
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | ~ m1_pre_topc(B_183,A_182)
      | ~ l1_pre_topc(A_182) ) ),
    inference(resolution,[status(thm)],[c_55,c_523])).

tff(c_558,plain,(
    ! [A_184,B_185,A_186,B_187] :
      ( '#skF_1'(A_184,B_185,k6_tmap_1(A_186,u1_struct_0(B_187))) = u1_struct_0(B_185)
      | k8_tmap_1(A_184,B_185) = k6_tmap_1(A_186,u1_struct_0(B_187))
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186)
      | ~ m1_pre_topc(B_187,A_186)
      | ~ l1_pre_topc(A_186) ) ),
    inference(resolution,[status(thm)],[c_43,c_544])).

tff(c_4,plain,(
    ! [A_1,B_13,C_19] :
      ( k6_tmap_1(A_1,'#skF_1'(A_1,B_13,C_19)) != C_19
      | k8_tmap_1(A_1,B_13) = C_19
      | ~ l1_pre_topc(C_19)
      | ~ v2_pre_topc(C_19)
      | ~ v1_pre_topc(C_19)
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_598,plain,(
    ! [A_186,B_187,A_184,B_185] :
      ( k6_tmap_1(A_186,u1_struct_0(B_187)) != k6_tmap_1(A_184,u1_struct_0(B_185))
      | k8_tmap_1(A_184,B_185) = k6_tmap_1(A_186,u1_struct_0(B_187))
      | ~ l1_pre_topc(k6_tmap_1(A_186,u1_struct_0(B_187)))
      | ~ v2_pre_topc(k6_tmap_1(A_186,u1_struct_0(B_187)))
      | ~ v1_pre_topc(k6_tmap_1(A_186,u1_struct_0(B_187)))
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | k8_tmap_1(A_184,B_185) = k6_tmap_1(A_186,u1_struct_0(B_187))
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186)
      | ~ m1_pre_topc(B_187,A_186)
      | ~ l1_pre_topc(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_4])).

tff(c_2201,plain,(
    ! [A_387,B_388] :
      ( k6_tmap_1(A_387,u1_struct_0(B_388)) = k8_tmap_1(A_387,B_388)
      | ~ l1_pre_topc(k6_tmap_1(A_387,u1_struct_0(B_388)))
      | ~ v2_pre_topc(k6_tmap_1(A_387,u1_struct_0(B_388)))
      | ~ v1_pre_topc(k6_tmap_1(A_387,u1_struct_0(B_388)))
      | ~ m1_pre_topc(B_388,A_387)
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387)
      | k6_tmap_1(A_387,u1_struct_0(B_388)) = k8_tmap_1(A_387,B_388)
      | ~ m1_pre_topc(B_388,A_387)
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387)
      | ~ m1_pre_topc(B_388,A_387)
      | ~ l1_pre_topc(A_387) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_598])).

tff(c_2239,plain,(
    ! [A_389,B_390] :
      ( ~ l1_pre_topc(k6_tmap_1(A_389,u1_struct_0(B_390)))
      | ~ v1_pre_topc(k6_tmap_1(A_389,u1_struct_0(B_390)))
      | k6_tmap_1(A_389,u1_struct_0(B_390)) = k8_tmap_1(A_389,B_390)
      | ~ v2_pre_topc(A_389)
      | v2_struct_0(A_389)
      | ~ m1_pre_topc(B_390,A_389)
      | ~ l1_pre_topc(A_389) ) ),
    inference(resolution,[status(thm)],[c_49,c_2201])).

tff(c_2277,plain,(
    ! [A_391,B_392] :
      ( ~ l1_pre_topc(k6_tmap_1(A_391,u1_struct_0(B_392)))
      | k6_tmap_1(A_391,u1_struct_0(B_392)) = k8_tmap_1(A_391,B_392)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391)
      | ~ m1_pre_topc(B_392,A_391)
      | ~ l1_pre_topc(A_391) ) ),
    inference(resolution,[status(thm)],[c_55,c_2239])).

tff(c_2315,plain,(
    ! [A_393,B_394] :
      ( k6_tmap_1(A_393,u1_struct_0(B_394)) = k8_tmap_1(A_393,B_394)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393)
      | ~ m1_pre_topc(B_394,A_393)
      | ~ l1_pre_topc(A_393) ) ),
    inference(resolution,[status(thm)],[c_43,c_2277])).

tff(c_56,plain,(
    ! [A_47,B_48] :
      ( u1_struct_0(k6_tmap_1(A_47,B_48)) = u1_struct_0(A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_60,plain,(
    ! [A_28,B_30] :
      ( u1_struct_0(k6_tmap_1(A_28,u1_struct_0(B_30))) = u1_struct_0(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_2679,plain,(
    ! [A_406,B_407] :
      ( u1_struct_0(k8_tmap_1(A_406,B_407)) = u1_struct_0(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406)
      | ~ m1_pre_topc(B_407,A_406)
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406)
      | ~ m1_pre_topc(B_407,A_406)
      | ~ l1_pre_topc(A_406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2315,c_60])).

tff(c_34,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_37,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2882,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2679,c_37])).

tff(c_2892,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_28,c_2882])).

tff(c_2894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2892])).

tff(c_2896,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2897,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2896,c_2897])).

tff(c_2908,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_4935,plain,(
    ! [A_513,B_514] :
      ( u1_pre_topc(k6_tmap_1(A_513,B_514)) = k5_tmap_1(A_513,B_514)
      | ~ m1_subset_1(B_514,k1_zfmisc_1(u1_struct_0(A_513)))
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4965,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) = k5_tmap_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2908,c_4935])).

tff(c_4986,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) = k5_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_4965])).

tff(c_4987,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) = k5_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4986])).

tff(c_2895,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4547,plain,(
    ! [A_499,B_500] :
      ( v1_pre_topc(k6_tmap_1(A_499,B_500))
      | ~ m1_subset_1(B_500,k1_zfmisc_1(u1_struct_0(A_499)))
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4565,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2908,c_4547])).

tff(c_4580,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_4565])).

tff(c_4581,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4580])).

tff(c_2977,plain,(
    ! [A_414,B_415] :
      ( v2_pre_topc(k6_tmap_1(A_414,B_415))
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2992,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2908,c_2977])).

tff(c_3001,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2992])).

tff(c_3002,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3001])).

tff(c_2950,plain,(
    ! [A_412,B_413] :
      ( l1_pre_topc(k6_tmap_1(A_412,B_413))
      | ~ m1_subset_1(B_413,k1_zfmisc_1(u1_struct_0(A_412)))
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2965,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2908,c_2950])).

tff(c_2974,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2965])).

tff(c_2975,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2974])).

tff(c_5022,plain,(
    ! [B_516,A_517,C_518] :
      ( u1_struct_0(B_516) = '#skF_1'(A_517,B_516,C_518)
      | k8_tmap_1(A_517,B_516) = C_518
      | ~ l1_pre_topc(C_518)
      | ~ v2_pre_topc(C_518)
      | ~ v1_pre_topc(C_518)
      | ~ m1_pre_topc(B_516,A_517)
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5030,plain,(
    ! [A_517,B_516] :
      ( '#skF_1'(A_517,B_516,k6_tmap_1('#skF_2','#skF_4')) = u1_struct_0(B_516)
      | k8_tmap_1(A_517,B_516) = k6_tmap_1('#skF_2','#skF_4')
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_516,A_517)
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517) ) ),
    inference(resolution,[status(thm)],[c_3002,c_5022])).

tff(c_7902,plain,(
    ! [A_677,B_678] :
      ( '#skF_1'(A_677,B_678,k6_tmap_1('#skF_2','#skF_4')) = u1_struct_0(B_678)
      | k8_tmap_1(A_677,B_678) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_678,A_677)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4581,c_2975,c_5030])).

tff(c_7917,plain,(
    ! [A_677,B_678] :
      ( k6_tmap_1(A_677,u1_struct_0(B_678)) != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_677,B_678) = k6_tmap_1('#skF_2','#skF_4')
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_678,A_677)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677)
      | k8_tmap_1(A_677,B_678) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_678,A_677)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7902,c_4])).

tff(c_7932,plain,(
    ! [A_680,B_681] :
      ( k6_tmap_1(A_680,u1_struct_0(B_681)) != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_680,B_681) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_681,A_680)
      | ~ l1_pre_topc(A_680)
      | ~ v2_pre_topc(A_680)
      | v2_struct_0(A_680) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4581,c_3002,c_2975,c_7917])).

tff(c_7960,plain,(
    ! [A_682] :
      ( k6_tmap_1(A_682,'#skF_4') != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_682,'#skF_3') = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_682)
      | ~ l1_pre_topc(A_682)
      | ~ v2_pre_topc(A_682)
      | v2_struct_0(A_682) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2895,c_7932])).

tff(c_7963,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_7960])).

tff(c_7966,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_7963])).

tff(c_7967,plain,(
    k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_7966])).

tff(c_2909,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_32,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != k5_tmap_1('#skF_2','#skF_4')
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2941,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != k5_tmap_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2909,c_32])).

tff(c_8004,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) != k5_tmap_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7967,c_2941])).

tff(c_8011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4987,c_8004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.09/5.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.11/6.00  
% 18.11/6.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.11/6.00  %$ m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 18.11/6.00  
% 18.11/6.00  %Foreground sorts:
% 18.11/6.00  
% 18.11/6.00  
% 18.11/6.00  %Background operators:
% 18.11/6.00  
% 18.11/6.00  
% 18.11/6.00  %Foreground operators:
% 18.11/6.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 18.11/6.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.11/6.00  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 18.11/6.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.11/6.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.11/6.00  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 18.11/6.00  tff('#skF_2', type, '#skF_2': $i).
% 18.11/6.00  tff('#skF_3', type, '#skF_3': $i).
% 18.11/6.00  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 18.11/6.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.11/6.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.11/6.00  tff('#skF_4', type, '#skF_4': $i).
% 18.11/6.00  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 18.11/6.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.11/6.00  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 18.11/6.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 18.11/6.00  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 18.11/6.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.11/6.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.11/6.00  
% 18.18/6.03  tff(f_110, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 18.18/6.03  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 18.18/6.03  tff(f_66, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 18.18/6.03  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 18.18/6.03  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 18.18/6.03  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.18/6.03  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.18/6.03  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.18/6.03  tff(c_22, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.18/6.03  tff(c_20, plain, (![B_30, A_28]: (m1_subset_1(u1_struct_0(B_30), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.18/6.03  tff(c_39, plain, (![A_37, B_38]: (l1_pre_topc(k6_tmap_1(A_37, B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.18/6.03  tff(c_43, plain, (![A_28, B_30]: (l1_pre_topc(k6_tmap_1(A_28, u1_struct_0(B_30))) | ~v2_pre_topc(A_28) | v2_struct_0(A_28) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_20, c_39])).
% 18.18/6.03  tff(c_51, plain, (![A_45, B_46]: (v1_pre_topc(k6_tmap_1(A_45, B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.18/6.03  tff(c_55, plain, (![A_28, B_30]: (v1_pre_topc(k6_tmap_1(A_28, u1_struct_0(B_30))) | ~v2_pre_topc(A_28) | v2_struct_0(A_28) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_20, c_51])).
% 18.18/6.03  tff(c_45, plain, (![A_41, B_42]: (v2_pre_topc(k6_tmap_1(A_41, B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.18/6.03  tff(c_49, plain, (![A_28, B_30]: (v2_pre_topc(k6_tmap_1(A_28, u1_struct_0(B_30))) | ~v2_pre_topc(A_28) | v2_struct_0(A_28) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_20, c_45])).
% 18.18/6.03  tff(c_112, plain, (![B_55, A_56, C_57]: (u1_struct_0(B_55)='#skF_1'(A_56, B_55, C_57) | k8_tmap_1(A_56, B_55)=C_57 | ~l1_pre_topc(C_57) | ~v2_pre_topc(C_57) | ~v1_pre_topc(C_57) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.18/6.03  tff(c_523, plain, (![A_172, B_173, A_174, B_175]: ('#skF_1'(A_172, B_173, k6_tmap_1(A_174, u1_struct_0(B_175)))=u1_struct_0(B_173) | k8_tmap_1(A_172, B_173)=k6_tmap_1(A_174, u1_struct_0(B_175)) | ~l1_pre_topc(k6_tmap_1(A_174, u1_struct_0(B_175))) | ~v1_pre_topc(k6_tmap_1(A_174, u1_struct_0(B_175))) | ~m1_pre_topc(B_173, A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | ~v2_pre_topc(A_174) | v2_struct_0(A_174) | ~m1_pre_topc(B_175, A_174) | ~l1_pre_topc(A_174))), inference(resolution, [status(thm)], [c_49, c_112])).
% 18.18/6.03  tff(c_544, plain, (![A_180, B_181, A_182, B_183]: ('#skF_1'(A_180, B_181, k6_tmap_1(A_182, u1_struct_0(B_183)))=u1_struct_0(B_181) | k8_tmap_1(A_180, B_181)=k6_tmap_1(A_182, u1_struct_0(B_183)) | ~l1_pre_topc(k6_tmap_1(A_182, u1_struct_0(B_183))) | ~m1_pre_topc(B_181, A_180) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | ~m1_pre_topc(B_183, A_182) | ~l1_pre_topc(A_182))), inference(resolution, [status(thm)], [c_55, c_523])).
% 18.18/6.03  tff(c_558, plain, (![A_184, B_185, A_186, B_187]: ('#skF_1'(A_184, B_185, k6_tmap_1(A_186, u1_struct_0(B_187)))=u1_struct_0(B_185) | k8_tmap_1(A_184, B_185)=k6_tmap_1(A_186, u1_struct_0(B_187)) | ~m1_pre_topc(B_185, A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | ~v2_pre_topc(A_186) | v2_struct_0(A_186) | ~m1_pre_topc(B_187, A_186) | ~l1_pre_topc(A_186))), inference(resolution, [status(thm)], [c_43, c_544])).
% 18.18/6.03  tff(c_4, plain, (![A_1, B_13, C_19]: (k6_tmap_1(A_1, '#skF_1'(A_1, B_13, C_19))!=C_19 | k8_tmap_1(A_1, B_13)=C_19 | ~l1_pre_topc(C_19) | ~v2_pre_topc(C_19) | ~v1_pre_topc(C_19) | ~m1_pre_topc(B_13, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.18/6.03  tff(c_598, plain, (![A_186, B_187, A_184, B_185]: (k6_tmap_1(A_186, u1_struct_0(B_187))!=k6_tmap_1(A_184, u1_struct_0(B_185)) | k8_tmap_1(A_184, B_185)=k6_tmap_1(A_186, u1_struct_0(B_187)) | ~l1_pre_topc(k6_tmap_1(A_186, u1_struct_0(B_187))) | ~v2_pre_topc(k6_tmap_1(A_186, u1_struct_0(B_187))) | ~v1_pre_topc(k6_tmap_1(A_186, u1_struct_0(B_187))) | ~m1_pre_topc(B_185, A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | k8_tmap_1(A_184, B_185)=k6_tmap_1(A_186, u1_struct_0(B_187)) | ~m1_pre_topc(B_185, A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | ~v2_pre_topc(A_186) | v2_struct_0(A_186) | ~m1_pre_topc(B_187, A_186) | ~l1_pre_topc(A_186))), inference(superposition, [status(thm), theory('equality')], [c_558, c_4])).
% 18.18/6.03  tff(c_2201, plain, (![A_387, B_388]: (k6_tmap_1(A_387, u1_struct_0(B_388))=k8_tmap_1(A_387, B_388) | ~l1_pre_topc(k6_tmap_1(A_387, u1_struct_0(B_388))) | ~v2_pre_topc(k6_tmap_1(A_387, u1_struct_0(B_388))) | ~v1_pre_topc(k6_tmap_1(A_387, u1_struct_0(B_388))) | ~m1_pre_topc(B_388, A_387) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387) | v2_struct_0(A_387) | k6_tmap_1(A_387, u1_struct_0(B_388))=k8_tmap_1(A_387, B_388) | ~m1_pre_topc(B_388, A_387) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387) | v2_struct_0(A_387) | ~v2_pre_topc(A_387) | v2_struct_0(A_387) | ~m1_pre_topc(B_388, A_387) | ~l1_pre_topc(A_387))), inference(reflexivity, [status(thm), theory('equality')], [c_598])).
% 18.18/6.03  tff(c_2239, plain, (![A_389, B_390]: (~l1_pre_topc(k6_tmap_1(A_389, u1_struct_0(B_390))) | ~v1_pre_topc(k6_tmap_1(A_389, u1_struct_0(B_390))) | k6_tmap_1(A_389, u1_struct_0(B_390))=k8_tmap_1(A_389, B_390) | ~v2_pre_topc(A_389) | v2_struct_0(A_389) | ~m1_pre_topc(B_390, A_389) | ~l1_pre_topc(A_389))), inference(resolution, [status(thm)], [c_49, c_2201])).
% 18.18/6.03  tff(c_2277, plain, (![A_391, B_392]: (~l1_pre_topc(k6_tmap_1(A_391, u1_struct_0(B_392))) | k6_tmap_1(A_391, u1_struct_0(B_392))=k8_tmap_1(A_391, B_392) | ~v2_pre_topc(A_391) | v2_struct_0(A_391) | ~m1_pre_topc(B_392, A_391) | ~l1_pre_topc(A_391))), inference(resolution, [status(thm)], [c_55, c_2239])).
% 18.18/6.03  tff(c_2315, plain, (![A_393, B_394]: (k6_tmap_1(A_393, u1_struct_0(B_394))=k8_tmap_1(A_393, B_394) | ~v2_pre_topc(A_393) | v2_struct_0(A_393) | ~m1_pre_topc(B_394, A_393) | ~l1_pre_topc(A_393))), inference(resolution, [status(thm)], [c_43, c_2277])).
% 18.18/6.03  tff(c_56, plain, (![A_47, B_48]: (u1_struct_0(k6_tmap_1(A_47, B_48))=u1_struct_0(A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.18/6.03  tff(c_60, plain, (![A_28, B_30]: (u1_struct_0(k6_tmap_1(A_28, u1_struct_0(B_30)))=u1_struct_0(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_20, c_56])).
% 18.18/6.03  tff(c_2679, plain, (![A_406, B_407]: (u1_struct_0(k8_tmap_1(A_406, B_407))=u1_struct_0(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406) | ~m1_pre_topc(B_407, A_406) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406) | ~m1_pre_topc(B_407, A_406) | ~l1_pre_topc(A_406))), inference(superposition, [status(thm), theory('equality')], [c_2315, c_60])).
% 18.18/6.03  tff(c_34, plain, (u1_struct_0('#skF_3')='#skF_4' | u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.18/6.03  tff(c_37, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 18.18/6.03  tff(c_2882, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2679, c_37])).
% 18.18/6.03  tff(c_2892, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_28, c_2882])).
% 18.18/6.03  tff(c_2894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2892])).
% 18.18/6.03  tff(c_2896, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 18.18/6.03  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.18/6.03  tff(c_2897, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 18.18/6.03  tff(c_2907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2896, c_2897])).
% 18.18/6.03  tff(c_2908, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_36])).
% 18.18/6.03  tff(c_4935, plain, (![A_513, B_514]: (u1_pre_topc(k6_tmap_1(A_513, B_514))=k5_tmap_1(A_513, B_514) | ~m1_subset_1(B_514, k1_zfmisc_1(u1_struct_0(A_513))) | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.18/6.03  tff(c_4965, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))=k5_tmap_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2908, c_4935])).
% 18.18/6.03  tff(c_4986, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))=k5_tmap_1('#skF_2', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_4965])).
% 18.18/6.03  tff(c_4987, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))=k5_tmap_1('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_4986])).
% 18.18/6.03  tff(c_2895, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 18.18/6.03  tff(c_4547, plain, (![A_499, B_500]: (v1_pre_topc(k6_tmap_1(A_499, B_500)) | ~m1_subset_1(B_500, k1_zfmisc_1(u1_struct_0(A_499))) | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.18/6.03  tff(c_4565, plain, (v1_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2908, c_4547])).
% 18.18/6.03  tff(c_4580, plain, (v1_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_4565])).
% 18.18/6.03  tff(c_4581, plain, (v1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_4580])).
% 18.18/6.03  tff(c_2977, plain, (![A_414, B_415]: (v2_pre_topc(k6_tmap_1(A_414, B_415)) | ~m1_subset_1(B_415, k1_zfmisc_1(u1_struct_0(A_414))) | ~l1_pre_topc(A_414) | ~v2_pre_topc(A_414) | v2_struct_0(A_414))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.18/6.03  tff(c_2992, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2908, c_2977])).
% 18.18/6.03  tff(c_3001, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2992])).
% 18.18/6.03  tff(c_3002, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_3001])).
% 18.18/6.03  tff(c_2950, plain, (![A_412, B_413]: (l1_pre_topc(k6_tmap_1(A_412, B_413)) | ~m1_subset_1(B_413, k1_zfmisc_1(u1_struct_0(A_412))) | ~l1_pre_topc(A_412) | ~v2_pre_topc(A_412) | v2_struct_0(A_412))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.18/6.03  tff(c_2965, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2908, c_2950])).
% 18.18/6.03  tff(c_2974, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2965])).
% 18.18/6.03  tff(c_2975, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_2974])).
% 18.18/6.03  tff(c_5022, plain, (![B_516, A_517, C_518]: (u1_struct_0(B_516)='#skF_1'(A_517, B_516, C_518) | k8_tmap_1(A_517, B_516)=C_518 | ~l1_pre_topc(C_518) | ~v2_pre_topc(C_518) | ~v1_pre_topc(C_518) | ~m1_pre_topc(B_516, A_517) | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.18/6.03  tff(c_5030, plain, (![A_517, B_516]: ('#skF_1'(A_517, B_516, k6_tmap_1('#skF_2', '#skF_4'))=u1_struct_0(B_516) | k8_tmap_1(A_517, B_516)=k6_tmap_1('#skF_2', '#skF_4') | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | ~v1_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | ~m1_pre_topc(B_516, A_517) | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517))), inference(resolution, [status(thm)], [c_3002, c_5022])).
% 18.18/6.03  tff(c_7902, plain, (![A_677, B_678]: ('#skF_1'(A_677, B_678, k6_tmap_1('#skF_2', '#skF_4'))=u1_struct_0(B_678) | k8_tmap_1(A_677, B_678)=k6_tmap_1('#skF_2', '#skF_4') | ~m1_pre_topc(B_678, A_677) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(demodulation, [status(thm), theory('equality')], [c_4581, c_2975, c_5030])).
% 18.18/6.03  tff(c_7917, plain, (![A_677, B_678]: (k6_tmap_1(A_677, u1_struct_0(B_678))!=k6_tmap_1('#skF_2', '#skF_4') | k8_tmap_1(A_677, B_678)=k6_tmap_1('#skF_2', '#skF_4') | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | ~v1_pre_topc(k6_tmap_1('#skF_2', '#skF_4')) | ~m1_pre_topc(B_678, A_677) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677) | k8_tmap_1(A_677, B_678)=k6_tmap_1('#skF_2', '#skF_4') | ~m1_pre_topc(B_678, A_677) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(superposition, [status(thm), theory('equality')], [c_7902, c_4])).
% 18.18/6.03  tff(c_7932, plain, (![A_680, B_681]: (k6_tmap_1(A_680, u1_struct_0(B_681))!=k6_tmap_1('#skF_2', '#skF_4') | k8_tmap_1(A_680, B_681)=k6_tmap_1('#skF_2', '#skF_4') | ~m1_pre_topc(B_681, A_680) | ~l1_pre_topc(A_680) | ~v2_pre_topc(A_680) | v2_struct_0(A_680))), inference(demodulation, [status(thm), theory('equality')], [c_4581, c_3002, c_2975, c_7917])).
% 18.18/6.03  tff(c_7960, plain, (![A_682]: (k6_tmap_1(A_682, '#skF_4')!=k6_tmap_1('#skF_2', '#skF_4') | k8_tmap_1(A_682, '#skF_3')=k6_tmap_1('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_3', A_682) | ~l1_pre_topc(A_682) | ~v2_pre_topc(A_682) | v2_struct_0(A_682))), inference(superposition, [status(thm), theory('equality')], [c_2895, c_7932])).
% 18.18/6.03  tff(c_7963, plain, (k8_tmap_1('#skF_2', '#skF_3')=k6_tmap_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_7960])).
% 18.18/6.03  tff(c_7966, plain, (k8_tmap_1('#skF_2', '#skF_3')=k6_tmap_1('#skF_2', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_7963])).
% 18.18/6.03  tff(c_7967, plain, (k8_tmap_1('#skF_2', '#skF_3')=k6_tmap_1('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_7966])).
% 18.18/6.03  tff(c_2909, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 18.18/6.03  tff(c_32, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))!=k5_tmap_1('#skF_2', '#skF_4') | u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.18/6.03  tff(c_2941, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))!=k5_tmap_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2909, c_32])).
% 18.18/6.03  tff(c_8004, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))!=k5_tmap_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7967, c_2941])).
% 18.18/6.03  tff(c_8011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4987, c_8004])).
% 18.18/6.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.18/6.03  
% 18.18/6.03  Inference rules
% 18.18/6.03  ----------------------
% 18.18/6.03  #Ref     : 1
% 18.18/6.03  #Sup     : 2277
% 18.18/6.03  #Fact    : 0
% 18.18/6.03  #Define  : 0
% 18.18/6.03  #Split   : 28
% 18.18/6.03  #Chain   : 0
% 18.18/6.04  #Close   : 0
% 18.18/6.04  
% 18.18/6.04  Ordering : KBO
% 18.18/6.04  
% 18.18/6.04  Simplification rules
% 18.18/6.04  ----------------------
% 18.18/6.04  #Subsume      : 487
% 18.18/6.04  #Demod        : 556
% 18.18/6.04  #Tautology    : 278
% 18.18/6.04  #SimpNegUnit  : 132
% 18.18/6.04  #BackRed      : 84
% 18.18/6.04  
% 18.18/6.04  #Partial instantiations: 0
% 18.18/6.04  #Strategies tried      : 1
% 18.18/6.04  
% 18.18/6.04  Timing (in seconds)
% 18.18/6.04  ----------------------
% 18.18/6.04  Preprocessing        : 0.49
% 18.18/6.04  Parsing              : 0.25
% 18.18/6.04  CNF conversion       : 0.04
% 18.18/6.04  Main loop            : 4.73
% 18.18/6.04  Inferencing          : 1.21
% 18.18/6.04  Reduction            : 0.95
% 18.18/6.04  Demodulation         : 0.62
% 18.18/6.04  BG Simplification    : 0.22
% 18.18/6.04  Subsumption          : 2.10
% 18.18/6.04  Abstraction          : 0.20
% 18.18/6.04  MUC search           : 0.00
% 18.18/6.04  Cooper               : 0.00
% 18.18/6.04  Total                : 5.28
% 18.18/6.04  Index Insertion      : 0.00
% 18.18/6.04  Index Deletion       : 0.00
% 18.18/6.04  Index Matching       : 0.00
% 18.18/6.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
