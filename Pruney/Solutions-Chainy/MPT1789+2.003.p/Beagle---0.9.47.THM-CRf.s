%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:48 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 146 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 409 expanded)
%              Number of equality atoms :   40 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
              & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_18,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2')
    | u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_55,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,(
    ! [A_25,B_26] :
      ( l1_pre_topc(k6_tmap_1(A_25,B_26))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_62,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_59])).

tff(c_63,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_62])).

tff(c_64,plain,(
    ! [A_27,B_28] :
      ( v1_pre_topc(k6_tmap_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_67,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_70,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_67])).

tff(c_71,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_70])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(u1_pre_topc(A_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_31,B_32] :
      ( g1_pre_topc(u1_struct_0(A_31),k5_tmap_1(A_31,B_32)) = k6_tmap_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_85,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_82])).

tff(c_86,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_85])).

tff(c_8,plain,(
    ! [C_7,A_3,D_8,B_4] :
      ( C_7 = A_3
      | g1_pre_topc(C_7,D_8) != g1_pre_topc(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k1_zfmisc_1(A_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_99,plain,(
    ! [A_33,B_34] :
      ( u1_struct_0('#skF_1') = A_33
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8])).

tff(c_109,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = u1_struct_0('#skF_1')
      | g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37)) != k6_tmap_1('#skF_1','#skF_2')
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_114,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = u1_struct_0('#skF_1')
      | k6_tmap_1('#skF_1','#skF_2') != A_38
      | ~ l1_pre_topc(A_38)
      | ~ v1_pre_topc(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_117,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_114])).

tff(c_120,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_117])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_120])).

tff(c_123,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_256,plain,(
    ! [A_56,B_57] :
      ( g1_pre_topc(u1_struct_0(A_56),k5_tmap_1(A_56,B_57)) = k6_tmap_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_260,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_256])).

tff(c_265,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_260])).

tff(c_266,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_265])).

tff(c_124,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_131,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_4])).

tff(c_135,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_158,plain,(
    ! [A_43,B_44] :
      ( l1_pre_topc(k6_tmap_1(A_43,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_158])).

tff(c_169,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_164])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_135,c_169])).

tff(c_172,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_173,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_187,plain,(
    ! [A_47,B_48] :
      ( v1_pre_topc(k6_tmap_1(A_47,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_193,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_187])).

tff(c_198,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_193])).

tff(c_199,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_198])).

tff(c_128,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_2])).

tff(c_215,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_199,c_128])).

tff(c_6,plain,(
    ! [D_8,B_4,C_7,A_3] :
      ( D_8 = B_4
      | g1_pre_topc(C_7,D_8) != g1_pre_topc(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k1_zfmisc_1(A_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_220,plain,(
    ! [D_8,C_7] :
      ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = D_8
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_7,D_8)
      | ~ m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_6])).

tff(c_228,plain,(
    ! [D_8,C_7] :
      ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = D_8
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_7,D_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_220])).

tff(c_269,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_228])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.25  
% 2.34/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.25  %$ m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.34/1.25  
% 2.34/1.25  %Foreground sorts:
% 2.34/1.25  
% 2.34/1.25  
% 2.34/1.25  %Background operators:
% 2.34/1.25  
% 2.34/1.25  
% 2.34/1.25  %Foreground operators:
% 2.34/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.34/1.25  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.34/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.25  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.34/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.25  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.34/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.25  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.34/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.34/1.25  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.34/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.25  
% 2.34/1.26  tff(f_86, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.34/1.26  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.34/1.26  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.34/1.26  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.34/1.27  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.34/1.27  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.34/1.27  tff(c_18, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))!=k5_tmap_1('#skF_1', '#skF_2') | u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.34/1.27  tff(c_55, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 2.34/1.27  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.34/1.27  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.34/1.27  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.34/1.27  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.34/1.27  tff(c_56, plain, (![A_25, B_26]: (l1_pre_topc(k6_tmap_1(A_25, B_26)) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.34/1.27  tff(c_59, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_56])).
% 2.34/1.27  tff(c_62, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_59])).
% 2.34/1.27  tff(c_63, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_62])).
% 2.34/1.27  tff(c_64, plain, (![A_27, B_28]: (v1_pre_topc(k6_tmap_1(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.34/1.27  tff(c_67, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_64])).
% 2.34/1.27  tff(c_70, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_67])).
% 2.34/1.27  tff(c_71, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_70])).
% 2.34/1.27  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.27  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_pre_topc(A_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2)))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.27  tff(c_80, plain, (![A_31, B_32]: (g1_pre_topc(u1_struct_0(A_31), k5_tmap_1(A_31, B_32))=k6_tmap_1(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.34/1.27  tff(c_82, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_80])).
% 2.34/1.27  tff(c_85, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_82])).
% 2.34/1.27  tff(c_86, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_85])).
% 2.34/1.27  tff(c_8, plain, (![C_7, A_3, D_8, B_4]: (C_7=A_3 | g1_pre_topc(C_7, D_8)!=g1_pre_topc(A_3, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(k1_zfmisc_1(A_3))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.27  tff(c_99, plain, (![A_33, B_34]: (u1_struct_0('#skF_1')=A_33 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(superposition, [status(thm), theory('equality')], [c_86, c_8])).
% 2.34/1.27  tff(c_109, plain, (![A_37]: (u1_struct_0(A_37)=u1_struct_0('#skF_1') | g1_pre_topc(u1_struct_0(A_37), u1_pre_topc(A_37))!=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_4, c_99])).
% 2.34/1.27  tff(c_114, plain, (![A_38]: (u1_struct_0(A_38)=u1_struct_0('#skF_1') | k6_tmap_1('#skF_1', '#skF_2')!=A_38 | ~l1_pre_topc(A_38) | ~v1_pre_topc(A_38) | ~l1_pre_topc(A_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_109])).
% 2.34/1.27  tff(c_117, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_114])).
% 2.34/1.27  tff(c_120, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_117])).
% 2.34/1.27  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_120])).
% 2.34/1.27  tff(c_123, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))!=k5_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 2.34/1.27  tff(c_256, plain, (![A_56, B_57]: (g1_pre_topc(u1_struct_0(A_56), k5_tmap_1(A_56, B_57))=k6_tmap_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.34/1.27  tff(c_260, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_256])).
% 2.34/1.27  tff(c_265, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_260])).
% 2.34/1.27  tff(c_266, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_265])).
% 2.34/1.27  tff(c_124, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 2.34/1.27  tff(c_131, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_4])).
% 2.34/1.27  tff(c_135, plain, (~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_131])).
% 2.34/1.27  tff(c_158, plain, (![A_43, B_44]: (l1_pre_topc(k6_tmap_1(A_43, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.34/1.27  tff(c_164, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_158])).
% 2.34/1.27  tff(c_169, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_164])).
% 2.34/1.27  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_135, c_169])).
% 2.34/1.27  tff(c_172, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_131])).
% 2.34/1.27  tff(c_173, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_131])).
% 2.34/1.27  tff(c_187, plain, (![A_47, B_48]: (v1_pre_topc(k6_tmap_1(A_47, B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.34/1.27  tff(c_193, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_187])).
% 2.34/1.27  tff(c_198, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_193])).
% 2.34/1.27  tff(c_199, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_198])).
% 2.34/1.27  tff(c_128, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_2])).
% 2.34/1.27  tff(c_215, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_199, c_128])).
% 2.34/1.27  tff(c_6, plain, (![D_8, B_4, C_7, A_3]: (D_8=B_4 | g1_pre_topc(C_7, D_8)!=g1_pre_topc(A_3, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(k1_zfmisc_1(A_3))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.27  tff(c_220, plain, (![D_8, C_7]: (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=D_8 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_7, D_8) | ~m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_215, c_6])).
% 2.34/1.27  tff(c_228, plain, (![D_8, C_7]: (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=D_8 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_7, D_8))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_220])).
% 2.34/1.27  tff(c_269, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_266, c_228])).
% 2.34/1.27  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_269])).
% 2.34/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.27  
% 2.34/1.27  Inference rules
% 2.34/1.27  ----------------------
% 2.34/1.27  #Ref     : 2
% 2.34/1.27  #Sup     : 57
% 2.34/1.27  #Fact    : 0
% 2.34/1.27  #Define  : 0
% 2.34/1.27  #Split   : 3
% 2.34/1.27  #Chain   : 0
% 2.34/1.27  #Close   : 0
% 2.34/1.27  
% 2.34/1.27  Ordering : KBO
% 2.34/1.27  
% 2.34/1.27  Simplification rules
% 2.34/1.27  ----------------------
% 2.34/1.27  #Subsume      : 3
% 2.34/1.27  #Demod        : 40
% 2.34/1.27  #Tautology    : 16
% 2.34/1.27  #SimpNegUnit  : 13
% 2.34/1.27  #BackRed      : 0
% 2.34/1.27  
% 2.34/1.27  #Partial instantiations: 0
% 2.34/1.27  #Strategies tried      : 1
% 2.34/1.27  
% 2.34/1.27  Timing (in seconds)
% 2.34/1.27  ----------------------
% 2.34/1.27  Preprocessing        : 0.28
% 2.34/1.27  Parsing              : 0.16
% 2.34/1.27  CNF conversion       : 0.02
% 2.34/1.27  Main loop            : 0.22
% 2.34/1.27  Inferencing          : 0.09
% 2.34/1.27  Reduction            : 0.06
% 2.34/1.27  Demodulation         : 0.04
% 2.34/1.27  BG Simplification    : 0.01
% 2.34/1.27  Subsumption          : 0.04
% 2.34/1.27  Abstraction          : 0.01
% 2.34/1.27  MUC search           : 0.00
% 2.34/1.27  Cooper               : 0.00
% 2.34/1.27  Total                : 0.54
% 2.34/1.27  Index Insertion      : 0.00
% 2.34/1.27  Index Deletion       : 0.00
% 2.34/1.27  Index Matching       : 0.00
% 2.34/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
