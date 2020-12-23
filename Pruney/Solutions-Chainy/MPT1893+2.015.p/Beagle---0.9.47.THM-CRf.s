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
% DateTime   : Thu Dec  3 10:30:27 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 207 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  175 ( 682 expanded)
%              Number of equality atoms :   19 (  45 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_134,negated_conjecture,(
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

tff(f_58,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_112,axiom,(
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

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [B_19] :
      ( ~ v1_subset_1(B_19,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_65,plain,(
    ! [B_31] :
      ( ~ v1_subset_1(B_31,B_31)
      | ~ r1_tarski(B_31,B_31) ) ),
    inference(resolution,[status(thm)],[c_61,c_30])).

tff(c_68,plain,(
    ! [B_31] : ~ v1_subset_1(B_31,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_201,plain,(
    ! [A_53,B_54] :
      ( k2_pre_topc(A_53,B_54) = B_54
      | ~ v4_pre_topc(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_201])).

tff(c_221,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_215])).

tff(c_222,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_59,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_111,plain,(
    ! [A_43,B_44] :
      ( k3_subset_1(A_43,k3_subset_1(A_43,B_44)) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_446,plain,(
    ! [B_77,A_78] :
      ( v4_pre_topc(B_77,A_78)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_78),B_77),A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_457,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_446])).

tff(c_459,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_59,c_457])).

tff(c_460,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_463,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_460])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_463])).

tff(c_471,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_472,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_765,plain,(
    ! [B_86,A_87] :
      ( v3_pre_topc(B_86,A_87)
      | ~ v4_pre_topc(B_86,A_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ v3_tdlat_3(A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_768,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_472,c_765])).

tff(c_785,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_52,c_471,c_768])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( v4_pre_topc(B_14,A_12)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_12),B_14),A_12)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_794,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_785,c_20])).

tff(c_797,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_794])).

tff(c_799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_797])).

tff(c_800,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_806,plain,(
    ! [A_88,B_89] :
      ( k2_pre_topc(A_88,B_89) = u1_struct_0(A_88)
      | ~ v1_tops_1(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_820,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_806])).

tff(c_826,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_800,c_820])).

tff(c_827,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_826])).

tff(c_44,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1307,plain,(
    ! [B_120,A_121] :
      ( v1_tops_1(B_120,A_121)
      | ~ v3_tex_2(B_120,A_121)
      | ~ v3_pre_topc(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1324,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1307])).

tff(c_1334,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_59,c_44,c_1324])).

tff(c_1336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_827,c_1334])).

tff(c_1337,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_70,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_79,plain,(
    ! [B_35,A_36] :
      ( B_35 = A_36
      | ~ r1_tarski(B_35,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ r1_tarski(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_79])).

tff(c_89,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_1340,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_89])).

tff(c_1346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1340])).

tff(c_1347,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_42,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1351,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_42])).

tff(c_1354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1351])).

tff(c_1356,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1355,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2031,plain,(
    ! [B_178,A_179] :
      ( v3_pre_topc(B_178,A_179)
      | ~ v4_pre_topc(B_178,A_179)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ v3_tdlat_3(A_179)
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2048,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2031])).

tff(c_2057,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_52,c_1355,c_2048])).

tff(c_2059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1356,c_2057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.70  
% 3.89/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.70  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.89/1.70  
% 3.89/1.70  %Foreground sorts:
% 3.89/1.70  
% 3.89/1.70  
% 3.89/1.70  %Background operators:
% 3.89/1.70  
% 3.89/1.70  
% 3.89/1.70  %Foreground operators:
% 3.89/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.89/1.70  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.89/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.70  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.89/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.89/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.89/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.70  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.89/1.70  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.89/1.70  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.89/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.70  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.89/1.70  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.89/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.89/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.89/1.70  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.89/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.70  
% 3.89/1.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.89/1.72  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.89/1.72  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.89/1.72  tff(f_134, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 3.89/1.72  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.89/1.72  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.89/1.72  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.89/1.72  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 3.89/1.72  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.89/1.72  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.89/1.72  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.89/1.72  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.72  tff(c_61, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.72  tff(c_30, plain, (![B_19]: (~v1_subset_1(B_19, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.89/1.72  tff(c_65, plain, (![B_31]: (~v1_subset_1(B_31, B_31) | ~r1_tarski(B_31, B_31))), inference(resolution, [status(thm)], [c_61, c_30])).
% 3.89/1.72  tff(c_68, plain, (![B_31]: (~v1_subset_1(B_31, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_65])).
% 3.89/1.72  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.72  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.72  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.72  tff(c_201, plain, (![A_53, B_54]: (k2_pre_topc(A_53, B_54)=B_54 | ~v4_pre_topc(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.89/1.72  tff(c_215, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_201])).
% 3.89/1.72  tff(c_221, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_215])).
% 3.89/1.72  tff(c_222, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_221])).
% 3.89/1.72  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.72  tff(c_52, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.72  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.89/1.72  tff(c_46, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.72  tff(c_59, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 3.89/1.72  tff(c_111, plain, (![A_43, B_44]: (k3_subset_1(A_43, k3_subset_1(A_43, B_44))=B_44 | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.89/1.72  tff(c_117, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_48, c_111])).
% 3.89/1.72  tff(c_446, plain, (![B_77, A_78]: (v4_pre_topc(B_77, A_78) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_78), B_77), A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.89/1.72  tff(c_457, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_117, c_446])).
% 3.89/1.72  tff(c_459, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_59, c_457])).
% 3.89/1.72  tff(c_460, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_459])).
% 3.89/1.72  tff(c_463, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_460])).
% 3.89/1.72  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_463])).
% 3.89/1.72  tff(c_471, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_459])).
% 3.89/1.72  tff(c_472, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_459])).
% 3.89/1.72  tff(c_765, plain, (![B_86, A_87]: (v3_pre_topc(B_86, A_87) | ~v4_pre_topc(B_86, A_87) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~v3_tdlat_3(A_87) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.89/1.72  tff(c_768, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_472, c_765])).
% 3.89/1.72  tff(c_785, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_52, c_471, c_768])).
% 3.89/1.72  tff(c_20, plain, (![B_14, A_12]: (v4_pre_topc(B_14, A_12) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_12), B_14), A_12) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.89/1.72  tff(c_794, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_785, c_20])).
% 3.89/1.72  tff(c_797, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_794])).
% 3.89/1.72  tff(c_799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_797])).
% 3.89/1.72  tff(c_800, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_221])).
% 3.89/1.72  tff(c_806, plain, (![A_88, B_89]: (k2_pre_topc(A_88, B_89)=u1_struct_0(A_88) | ~v1_tops_1(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.89/1.72  tff(c_820, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_806])).
% 3.89/1.72  tff(c_826, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_800, c_820])).
% 3.89/1.72  tff(c_827, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_826])).
% 3.89/1.72  tff(c_44, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.72  tff(c_1307, plain, (![B_120, A_121]: (v1_tops_1(B_120, A_121) | ~v3_tex_2(B_120, A_121) | ~v3_pre_topc(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.89/1.72  tff(c_1324, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1307])).
% 3.89/1.72  tff(c_1334, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_59, c_44, c_1324])).
% 3.89/1.72  tff(c_1336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_827, c_1334])).
% 3.89/1.72  tff(c_1337, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_826])).
% 3.89/1.72  tff(c_70, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.72  tff(c_78, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_70])).
% 3.89/1.72  tff(c_79, plain, (![B_35, A_36]: (B_35=A_36 | ~r1_tarski(B_35, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.72  tff(c_84, plain, (u1_struct_0('#skF_2')='#skF_3' | ~r1_tarski(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_78, c_79])).
% 3.89/1.72  tff(c_89, plain, (~r1_tarski(u1_struct_0('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_84])).
% 3.89/1.72  tff(c_1340, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_89])).
% 3.89/1.72  tff(c_1346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1340])).
% 3.89/1.72  tff(c_1347, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_84])).
% 3.89/1.72  tff(c_42, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.72  tff(c_1351, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_42])).
% 3.89/1.72  tff(c_1354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1351])).
% 3.89/1.72  tff(c_1356, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.89/1.72  tff(c_1355, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.89/1.72  tff(c_2031, plain, (![B_178, A_179]: (v3_pre_topc(B_178, A_179) | ~v4_pre_topc(B_178, A_179) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~v3_tdlat_3(A_179) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.89/1.72  tff(c_2048, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2031])).
% 3.89/1.72  tff(c_2057, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_52, c_1355, c_2048])).
% 3.89/1.72  tff(c_2059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1356, c_2057])).
% 3.89/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.72  
% 3.89/1.72  Inference rules
% 3.89/1.72  ----------------------
% 3.89/1.72  #Ref     : 0
% 3.89/1.72  #Sup     : 396
% 3.89/1.72  #Fact    : 0
% 3.89/1.72  #Define  : 0
% 3.89/1.72  #Split   : 14
% 3.89/1.72  #Chain   : 0
% 3.89/1.72  #Close   : 0
% 3.89/1.72  
% 3.89/1.72  Ordering : KBO
% 3.89/1.72  
% 3.89/1.72  Simplification rules
% 3.89/1.72  ----------------------
% 3.89/1.72  #Subsume      : 48
% 3.89/1.72  #Demod        : 353
% 3.89/1.72  #Tautology    : 168
% 3.89/1.72  #SimpNegUnit  : 40
% 3.89/1.72  #BackRed      : 23
% 3.89/1.72  
% 3.89/1.72  #Partial instantiations: 0
% 3.89/1.72  #Strategies tried      : 1
% 3.89/1.72  
% 3.89/1.72  Timing (in seconds)
% 3.89/1.72  ----------------------
% 3.89/1.72  Preprocessing        : 0.32
% 3.89/1.72  Parsing              : 0.17
% 3.89/1.72  CNF conversion       : 0.02
% 3.89/1.72  Main loop            : 0.61
% 3.89/1.72  Inferencing          : 0.23
% 3.89/1.72  Reduction            : 0.19
% 3.89/1.72  Demodulation         : 0.13
% 3.89/1.72  BG Simplification    : 0.03
% 3.89/1.72  Subsumption          : 0.10
% 3.89/1.72  Abstraction          : 0.03
% 3.89/1.72  MUC search           : 0.00
% 3.89/1.72  Cooper               : 0.00
% 3.89/1.72  Total                : 0.97
% 3.89/1.72  Index Insertion      : 0.00
% 3.89/1.72  Index Deletion       : 0.00
% 3.89/1.72  Index Matching       : 0.00
% 3.89/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
