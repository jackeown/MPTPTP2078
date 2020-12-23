%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:29 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 218 expanded)
%              Number of leaves         :   31 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 759 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_subset_1(k2_subset_1(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,(
    ! [A_6] : ~ v1_subset_1(A_6,A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_81,plain,(
    ! [A_33,B_34] :
      ( k2_pre_topc(A_33,B_34) = B_34
      | ~ v4_pre_topc(B_34,A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_81])).

tff(c_96,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_91])).

tff(c_97,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k3_subset_1(A_2,B_3),k1_zfmisc_1(A_2))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_59,plain,(
    ! [A_26,B_27] :
      ( k3_subset_1(A_26,k3_subset_1(A_26,B_27)) = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_170,plain,(
    ! [B_41,A_42] :
      ( v4_pre_topc(B_41,A_42)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_42),B_41),A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_177,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_170])).

tff(c_179,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_58,c_177])).

tff(c_180,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_183,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4,c_180])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_183])).

tff(c_188,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_189,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_262,plain,(
    ! [B_48,A_49] :
      ( v3_pre_topc(B_48,A_49)
      | ~ v4_pre_topc(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ v3_tdlat_3(A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_265,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_189,c_262])).

tff(c_278,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_188,c_265])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( v4_pre_topc(B_12,A_10)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_10),B_12),A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_286,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_278,c_14])).

tff(c_289,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_286])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_289])).

tff(c_292,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_336,plain,(
    ! [B_52,A_53] :
      ( v1_tops_1(B_52,A_53)
      | k2_pre_topc(A_53,B_52) != u1_struct_0(A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_346,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_336])).

tff(c_351,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | u1_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_292,c_346])).

tff(c_368,plain,(
    u1_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_352,plain,(
    ! [A_54,B_55] :
      ( k2_pre_topc(A_54,B_55) = u1_struct_0(A_54)
      | ~ v1_tops_1(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_362,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_352])).

tff(c_367,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_292,c_362])).

tff(c_369,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_367])).

tff(c_34,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_530,plain,(
    ! [B_69,A_70] :
      ( v1_tops_1(B_69,A_70)
      | ~ v3_tex_2(B_69,A_70)
      | ~ v3_pre_topc(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_543,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_530])).

tff(c_552,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_58,c_34,c_543])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_369,c_552])).

tff(c_555,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_558,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_367])).

tff(c_32,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_561,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_32])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_561])).

tff(c_565,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_564,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_769,plain,(
    ! [B_94,A_95] :
      ( v3_pre_topc(B_94,A_95)
      | ~ v4_pre_topc(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v3_tdlat_3(A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_782,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_769])).

tff(c_790,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_564,c_782])).

tff(c_792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.42  
% 3.05/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.42  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.05/1.42  
% 3.05/1.42  %Foreground sorts:
% 3.05/1.42  
% 3.05/1.42  
% 3.05/1.42  %Background operators:
% 3.05/1.42  
% 3.05/1.42  
% 3.05/1.42  %Foreground operators:
% 3.05/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.05/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.05/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.05/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.05/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.05/1.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.05/1.42  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.05/1.42  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.05/1.42  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.42  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.42  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.05/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.05/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.05/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.05/1.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.05/1.42  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.05/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.42  
% 3.05/1.44  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.05/1.44  tff(f_38, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.05/1.44  tff(f_122, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 3.05/1.44  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.05/1.44  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.05/1.44  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.05/1.44  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 3.05/1.44  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.05/1.44  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 3.05/1.44  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 3.05/1.44  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.44  tff(c_8, plain, (![A_6]: (~v1_subset_1(k2_subset_1(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.44  tff(c_47, plain, (![A_6]: (~v1_subset_1(A_6, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 3.05/1.44  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.05/1.44  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.05/1.44  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.05/1.44  tff(c_81, plain, (![A_33, B_34]: (k2_pre_topc(A_33, B_34)=B_34 | ~v4_pre_topc(B_34, A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.05/1.44  tff(c_91, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_81])).
% 3.05/1.44  tff(c_96, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_91])).
% 3.05/1.44  tff(c_97, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_96])).
% 3.05/1.44  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.05/1.44  tff(c_42, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.05/1.44  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k3_subset_1(A_2, B_3), k1_zfmisc_1(A_2)) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.44  tff(c_36, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.05/1.44  tff(c_58, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 3.05/1.44  tff(c_59, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_subset_1(A_26, B_27))=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.44  tff(c_62, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_38, c_59])).
% 3.05/1.44  tff(c_170, plain, (![B_41, A_42]: (v4_pre_topc(B_41, A_42) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_42), B_41), A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.05/1.44  tff(c_177, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_62, c_170])).
% 3.05/1.44  tff(c_179, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_58, c_177])).
% 3.05/1.44  tff(c_180, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_179])).
% 3.05/1.44  tff(c_183, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_4, c_180])).
% 3.05/1.44  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_183])).
% 3.05/1.44  tff(c_188, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_179])).
% 3.05/1.44  tff(c_189, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_179])).
% 3.05/1.44  tff(c_262, plain, (![B_48, A_49]: (v3_pre_topc(B_48, A_49) | ~v4_pre_topc(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_49))) | ~v3_tdlat_3(A_49) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.05/1.44  tff(c_265, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_189, c_262])).
% 3.05/1.44  tff(c_278, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_188, c_265])).
% 3.05/1.44  tff(c_14, plain, (![B_12, A_10]: (v4_pre_topc(B_12, A_10) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_10), B_12), A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.05/1.44  tff(c_286, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_278, c_14])).
% 3.05/1.44  tff(c_289, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_286])).
% 3.05/1.44  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_289])).
% 3.05/1.44  tff(c_292, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_96])).
% 3.05/1.44  tff(c_336, plain, (![B_52, A_53]: (v1_tops_1(B_52, A_53) | k2_pre_topc(A_53, B_52)!=u1_struct_0(A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.05/1.44  tff(c_346, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_336])).
% 3.05/1.44  tff(c_351, plain, (v1_tops_1('#skF_3', '#skF_2') | u1_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_292, c_346])).
% 3.05/1.44  tff(c_368, plain, (u1_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_351])).
% 3.05/1.44  tff(c_352, plain, (![A_54, B_55]: (k2_pre_topc(A_54, B_55)=u1_struct_0(A_54) | ~v1_tops_1(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.05/1.44  tff(c_362, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_352])).
% 3.05/1.44  tff(c_367, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_292, c_362])).
% 3.05/1.44  tff(c_369, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_368, c_367])).
% 3.05/1.44  tff(c_34, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.05/1.44  tff(c_530, plain, (![B_69, A_70]: (v1_tops_1(B_69, A_70) | ~v3_tex_2(B_69, A_70) | ~v3_pre_topc(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.05/1.44  tff(c_543, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_530])).
% 3.05/1.44  tff(c_552, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_58, c_34, c_543])).
% 3.05/1.44  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_369, c_552])).
% 3.05/1.44  tff(c_555, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_351])).
% 3.05/1.44  tff(c_558, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_555, c_367])).
% 3.05/1.44  tff(c_32, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.05/1.44  tff(c_561, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_32])).
% 3.05/1.44  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_561])).
% 3.05/1.44  tff(c_565, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 3.05/1.44  tff(c_564, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 3.05/1.44  tff(c_769, plain, (![B_94, A_95]: (v3_pre_topc(B_94, A_95) | ~v4_pre_topc(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~v3_tdlat_3(A_95) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.05/1.44  tff(c_782, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_769])).
% 3.05/1.44  tff(c_790, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_564, c_782])).
% 3.05/1.44  tff(c_792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_790])).
% 3.05/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.44  
% 3.05/1.44  Inference rules
% 3.05/1.44  ----------------------
% 3.05/1.44  #Ref     : 0
% 3.05/1.44  #Sup     : 146
% 3.05/1.44  #Fact    : 0
% 3.05/1.44  #Define  : 0
% 3.05/1.44  #Split   : 11
% 3.05/1.44  #Chain   : 0
% 3.05/1.44  #Close   : 0
% 3.05/1.44  
% 3.05/1.44  Ordering : KBO
% 3.05/1.44  
% 3.05/1.44  Simplification rules
% 3.05/1.44  ----------------------
% 3.05/1.44  #Subsume      : 14
% 3.05/1.44  #Demod        : 122
% 3.05/1.44  #Tautology    : 64
% 3.05/1.44  #SimpNegUnit  : 15
% 3.05/1.44  #BackRed      : 3
% 3.05/1.44  
% 3.05/1.44  #Partial instantiations: 0
% 3.05/1.44  #Strategies tried      : 1
% 3.05/1.44  
% 3.05/1.44  Timing (in seconds)
% 3.05/1.44  ----------------------
% 3.05/1.44  Preprocessing        : 0.32
% 3.05/1.44  Parsing              : 0.18
% 3.05/1.44  CNF conversion       : 0.02
% 3.05/1.44  Main loop            : 0.35
% 3.05/1.44  Inferencing          : 0.13
% 3.05/1.44  Reduction            : 0.11
% 3.05/1.44  Demodulation         : 0.07
% 3.05/1.44  BG Simplification    : 0.02
% 3.05/1.44  Subsumption          : 0.06
% 3.05/1.44  Abstraction          : 0.02
% 3.05/1.44  MUC search           : 0.00
% 3.05/1.44  Cooper               : 0.00
% 3.05/1.44  Total                : 0.71
% 3.05/1.44  Index Insertion      : 0.00
% 3.05/1.44  Index Deletion       : 0.00
% 3.05/1.44  Index Matching       : 0.00
% 3.05/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
