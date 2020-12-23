%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:26 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 212 expanded)
%              Number of leaves         :   40 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  184 ( 683 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_150,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_60,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    ! [A_42,B_43] :
      ( k3_subset_1(A_42,k3_subset_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_101])).

tff(c_108,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_105])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_247,plain,(
    ! [A_67,B_68] :
      ( k2_pre_topc(A_67,B_68) = B_68
      | ~ v4_pre_topc(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_261,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_247])).

tff(c_271,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_261])).

tff(c_273,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_87,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_106,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_101])).

tff(c_463,plain,(
    ! [B_92,A_93] :
      ( v4_pre_topc(B_92,A_93)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_93),B_92),A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_477,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_463])).

tff(c_486,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_87,c_477])).

tff(c_517,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_546,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_517])).

tff(c_550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_546])).

tff(c_551,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_552,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_602,plain,(
    ! [B_101,A_102] :
      ( v3_pre_topc(B_101,A_102)
      | ~ v4_pre_topc(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tdlat_3(A_102)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_605,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_552,c_602])).

tff(c_626,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_551,c_605])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( v4_pre_topc(B_20,A_18)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_18),B_20),A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_636,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_626,c_24])).

tff(c_639,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_636])).

tff(c_641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_639])).

tff(c_642,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_648,plain,(
    ! [A_103,B_104] :
      ( k2_pre_topc(A_103,B_104) = u1_struct_0(A_103)
      | ~ v1_tops_1(B_104,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_662,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_648])).

tff(c_672,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_642,c_662])).

tff(c_674,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_672])).

tff(c_46,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1050,plain,(
    ! [B_144,A_145] :
      ( v1_tops_1(B_144,A_145)
      | ~ v3_tex_2(B_144,A_145)
      | ~ v3_pre_topc(B_144,A_145)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1067,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1050])).

tff(c_1081,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_87,c_46,c_1067])).

tff(c_1083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_674,c_1081])).

tff(c_1084,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_672])).

tff(c_44,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_88,plain,(
    ! [B_38,A_39] :
      ( ~ v1_subset_1(B_38,A_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,
    ( ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_97,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_91])).

tff(c_219,plain,(
    ! [A_64,B_65] :
      ( ~ v1_xboole_0(k3_subset_1(A_64,B_65))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64))
      | ~ v1_subset_1(B_65,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_231,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_219])).

tff(c_242,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_231])).

tff(c_243,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_242])).

tff(c_1086,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_243])).

tff(c_1094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_108,c_1086])).

tff(c_1096,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1095,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1568,plain,(
    ! [B_204,A_205] :
      ( v3_pre_topc(B_204,A_205)
      | ~ v4_pre_topc(B_204,A_205)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ v3_tdlat_3(A_205)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1585,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1568])).

tff(c_1598,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_1095,c_1585])).

tff(c_1600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1096,c_1598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:02:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.64  
% 3.64/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.65  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.64/1.65  
% 3.64/1.65  %Foreground sorts:
% 3.64/1.65  
% 3.64/1.65  
% 3.64/1.65  %Background operators:
% 3.64/1.65  
% 3.64/1.65  
% 3.64/1.65  %Foreground operators:
% 3.64/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.64/1.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.65  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.64/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.64/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.64/1.65  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.64/1.65  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.64/1.65  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.64/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.65  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.64/1.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.65  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.64/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.64/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.64/1.65  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.64/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.64/1.65  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.64/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.65  
% 3.64/1.66  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.64/1.66  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.64/1.66  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.64/1.66  tff(f_40, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.64/1.66  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.64/1.66  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.64/1.66  tff(f_150, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 3.64/1.66  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.64/1.66  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.64/1.66  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 3.64/1.66  tff(f_112, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.64/1.66  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.64/1.66  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.64/1.66  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 3.64/1.66  tff(f_99, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 3.64/1.66  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.64/1.66  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.64/1.66  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.64/1.66  tff(c_12, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.64/1.66  tff(c_59, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 3.64/1.66  tff(c_60, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_59])).
% 3.64/1.66  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.64/1.66  tff(c_101, plain, (![A_42, B_43]: (k3_subset_1(A_42, k3_subset_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.64/1.66  tff(c_105, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_101])).
% 3.64/1.66  tff(c_108, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_105])).
% 3.64/1.66  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.66  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.66  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.66  tff(c_247, plain, (![A_67, B_68]: (k2_pre_topc(A_67, B_68)=B_68 | ~v4_pre_topc(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.64/1.66  tff(c_261, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_247])).
% 3.64/1.66  tff(c_271, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_261])).
% 3.64/1.66  tff(c_273, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_271])).
% 3.64/1.66  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.66  tff(c_54, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.66  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.66  tff(c_48, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.66  tff(c_87, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 3.64/1.66  tff(c_106, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_50, c_101])).
% 3.64/1.66  tff(c_463, plain, (![B_92, A_93]: (v4_pre_topc(B_92, A_93) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_93), B_92), A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.64/1.66  tff(c_477, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_106, c_463])).
% 3.64/1.66  tff(c_486, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_87, c_477])).
% 3.64/1.66  tff(c_517, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_486])).
% 3.64/1.66  tff(c_546, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_517])).
% 3.64/1.66  tff(c_550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_546])).
% 3.64/1.66  tff(c_551, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_486])).
% 3.64/1.66  tff(c_552, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_486])).
% 3.64/1.66  tff(c_602, plain, (![B_101, A_102]: (v3_pre_topc(B_101, A_102) | ~v4_pre_topc(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~v3_tdlat_3(A_102) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.64/1.66  tff(c_605, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_552, c_602])).
% 3.64/1.66  tff(c_626, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_551, c_605])).
% 3.64/1.66  tff(c_24, plain, (![B_20, A_18]: (v4_pre_topc(B_20, A_18) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_18), B_20), A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.64/1.66  tff(c_636, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_626, c_24])).
% 3.64/1.66  tff(c_639, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_636])).
% 3.64/1.66  tff(c_641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_639])).
% 3.64/1.66  tff(c_642, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_271])).
% 3.64/1.66  tff(c_648, plain, (![A_103, B_104]: (k2_pre_topc(A_103, B_104)=u1_struct_0(A_103) | ~v1_tops_1(B_104, A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.64/1.66  tff(c_662, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_648])).
% 3.64/1.66  tff(c_672, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_642, c_662])).
% 3.64/1.66  tff(c_674, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_672])).
% 3.64/1.66  tff(c_46, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.66  tff(c_1050, plain, (![B_144, A_145]: (v1_tops_1(B_144, A_145) | ~v3_tex_2(B_144, A_145) | ~v3_pre_topc(B_144, A_145) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.64/1.66  tff(c_1067, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1050])).
% 3.64/1.66  tff(c_1081, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_87, c_46, c_1067])).
% 3.64/1.66  tff(c_1083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_674, c_1081])).
% 3.64/1.66  tff(c_1084, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_672])).
% 3.64/1.66  tff(c_44, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.66  tff(c_88, plain, (![B_38, A_39]: (~v1_subset_1(B_38, A_39) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.64/1.66  tff(c_91, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_88])).
% 3.64/1.66  tff(c_97, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_91])).
% 3.64/1.66  tff(c_219, plain, (![A_64, B_65]: (~v1_xboole_0(k3_subset_1(A_64, B_65)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)) | ~v1_subset_1(B_65, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.64/1.66  tff(c_231, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_219])).
% 3.64/1.66  tff(c_242, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_231])).
% 3.64/1.66  tff(c_243, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_97, c_242])).
% 3.64/1.66  tff(c_1086, plain, (~v1_xboole_0(k3_subset_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_243])).
% 3.64/1.66  tff(c_1094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_108, c_1086])).
% 3.64/1.66  tff(c_1096, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 3.64/1.66  tff(c_1095, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 3.64/1.66  tff(c_1568, plain, (![B_204, A_205]: (v3_pre_topc(B_204, A_205) | ~v4_pre_topc(B_204, A_205) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_205))) | ~v3_tdlat_3(A_205) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.64/1.66  tff(c_1585, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1568])).
% 3.64/1.66  tff(c_1598, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_1095, c_1585])).
% 3.64/1.66  tff(c_1600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1096, c_1598])).
% 3.64/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.66  
% 3.64/1.66  Inference rules
% 3.64/1.66  ----------------------
% 3.64/1.66  #Ref     : 0
% 3.64/1.66  #Sup     : 304
% 3.64/1.66  #Fact    : 0
% 3.64/1.66  #Define  : 0
% 3.64/1.66  #Split   : 14
% 3.64/1.66  #Chain   : 0
% 3.64/1.66  #Close   : 0
% 3.64/1.66  
% 3.64/1.66  Ordering : KBO
% 3.64/1.66  
% 3.64/1.66  Simplification rules
% 3.64/1.66  ----------------------
% 3.64/1.66  #Subsume      : 35
% 3.64/1.66  #Demod        : 193
% 3.64/1.66  #Tautology    : 108
% 3.64/1.66  #SimpNegUnit  : 18
% 3.64/1.66  #BackRed      : 6
% 3.64/1.66  
% 3.64/1.66  #Partial instantiations: 0
% 3.64/1.66  #Strategies tried      : 1
% 3.64/1.66  
% 3.64/1.66  Timing (in seconds)
% 3.64/1.66  ----------------------
% 3.64/1.67  Preprocessing        : 0.35
% 3.64/1.67  Parsing              : 0.19
% 3.64/1.67  CNF conversion       : 0.02
% 3.64/1.67  Main loop            : 0.50
% 3.64/1.67  Inferencing          : 0.20
% 3.64/1.67  Reduction            : 0.16
% 3.64/1.67  Demodulation         : 0.11
% 3.64/1.67  BG Simplification    : 0.02
% 3.64/1.67  Subsumption          : 0.08
% 3.64/1.67  Abstraction          : 0.02
% 3.64/1.67  MUC search           : 0.00
% 3.64/1.67  Cooper               : 0.00
% 3.64/1.67  Total                : 0.89
% 3.64/1.67  Index Insertion      : 0.00
% 3.64/1.67  Index Deletion       : 0.00
% 3.64/1.67  Index Matching       : 0.00
% 3.64/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
