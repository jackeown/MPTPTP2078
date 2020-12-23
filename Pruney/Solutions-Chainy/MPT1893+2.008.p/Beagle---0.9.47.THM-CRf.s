%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:26 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 238 expanded)
%              Number of leaves         :   44 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  202 ( 762 expanded)
%              Number of equality atoms :   31 (  61 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_156,negated_conjecture,(
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

tff(f_77,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_28,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_134,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_9] : k3_subset_1(A_9,k1_subset_1(A_9)) = k2_subset_1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_9] : k3_subset_1(A_9,k1_subset_1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_66,plain,(
    ! [A_9] : k3_subset_1(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_133,plain,(
    ! [A_54,B_55] :
      ( k3_subset_1(A_54,k3_subset_1(A_54,B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_139,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_133])).

tff(c_143,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_139])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_386,plain,(
    ! [A_82,B_83] :
      ( k2_pre_topc(A_82,B_83) = B_83
      | ~ v4_pre_topc(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_396,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_386])).

tff(c_405,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_396])).

tff(c_407,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_60,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_222,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k3_subset_1(A_70,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_233,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_222])).

tff(c_4,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_271,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_4])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_94,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_141,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_56,c_133])).

tff(c_518,plain,(
    ! [B_96,A_97] :
      ( v4_pre_topc(B_96,A_97)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_97),B_96),A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_525,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_518])).

tff(c_535,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_94,c_525])).

tff(c_624,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_627,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_624])).

tff(c_631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_627])).

tff(c_632,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_633,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_872,plain,(
    ! [B_119,A_120] :
      ( v3_pre_topc(B_119,A_120)
      | ~ v4_pre_topc(B_119,A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ v3_tdlat_3(A_120)
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_875,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_633,c_872])).

tff(c_892,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_60,c_632,c_875])).

tff(c_30,plain,(
    ! [B_24,A_22] :
      ( v4_pre_topc(B_24,A_22)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_22),B_24),A_22)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_901,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_892,c_30])).

tff(c_904,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_901])).

tff(c_906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_904])).

tff(c_907,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_913,plain,(
    ! [B_121,A_122] :
      ( v1_tops_1(B_121,A_122)
      | k2_pre_topc(A_122,B_121) != u1_struct_0(A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_923,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_913])).

tff(c_932,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | u1_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_907,c_923])).

tff(c_934,plain,(
    u1_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_932])).

tff(c_990,plain,(
    ! [A_128,B_129] :
      ( k2_pre_topc(A_128,B_129) = u1_struct_0(A_128)
      | ~ v1_tops_1(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1000,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_990])).

tff(c_1009,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_907,c_1000])).

tff(c_1010,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_1009])).

tff(c_52,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1407,plain,(
    ! [B_160,A_161] :
      ( v1_tops_1(B_160,A_161)
      | ~ v3_tex_2(B_160,A_161)
      | ~ v3_pre_topc(B_160,A_161)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1420,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1407])).

tff(c_1433,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_94,c_52,c_1420])).

tff(c_1435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1010,c_1433])).

tff(c_1437,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_932])).

tff(c_50,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_110,plain,(
    ! [B_49,A_50] :
      ( ~ v1_subset_1(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_116,plain,
    ( ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_110])).

tff(c_123,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_116])).

tff(c_275,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(k3_subset_1(A_75,B_76))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75))
      | ~ v1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_284,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_275])).

tff(c_292,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_284])).

tff(c_293,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_292])).

tff(c_1439,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_293])).

tff(c_1451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_143,c_1439])).

tff(c_1453,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1452,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2448,plain,(
    ! [B_253,A_254] :
      ( v3_pre_topc(B_253,A_254)
      | ~ v4_pre_topc(B_253,A_254)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ v3_tdlat_3(A_254)
      | ~ l1_pre_topc(A_254)
      | ~ v2_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2458,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2448])).

tff(c_2467,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_60,c_1452,c_2458])).

tff(c_2469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1453,c_2467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.79  
% 4.08/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.80  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.08/1.80  
% 4.08/1.80  %Foreground sorts:
% 4.08/1.80  
% 4.08/1.80  
% 4.08/1.80  %Background operators:
% 4.08/1.80  
% 4.08/1.80  
% 4.08/1.80  %Foreground operators:
% 4.08/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.08/1.80  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.08/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.08/1.80  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.08/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.08/1.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.08/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.08/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.08/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.08/1.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.08/1.80  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.08/1.80  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.08/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.08/1.80  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.08/1.80  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.08/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.80  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.08/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.08/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.08/1.80  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.08/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.08/1.80  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.08/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.08/1.80  
% 4.08/1.81  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.08/1.81  tff(f_30, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.08/1.81  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.08/1.81  tff(f_42, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 4.08/1.81  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.08/1.81  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.08/1.81  tff(f_156, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 4.08/1.81  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.08/1.81  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.08/1.81  tff(f_28, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.08/1.81  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.08/1.81  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 4.08/1.81  tff(f_118, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 4.08/1.81  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.08/1.81  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 4.08/1.81  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 4.08/1.81  tff(f_105, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tex_2)).
% 4.08/1.81  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.08/1.81  tff(c_6, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.08/1.81  tff(c_8, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.08/1.81  tff(c_14, plain, (![A_9]: (k3_subset_1(A_9, k1_subset_1(A_9))=k2_subset_1(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.08/1.81  tff(c_65, plain, (![A_9]: (k3_subset_1(A_9, k1_subset_1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 4.08/1.81  tff(c_66, plain, (![A_9]: (k3_subset_1(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_65])).
% 4.08/1.81  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.08/1.81  tff(c_133, plain, (![A_54, B_55]: (k3_subset_1(A_54, k3_subset_1(A_54, B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.08/1.81  tff(c_139, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_133])).
% 4.08/1.81  tff(c_143, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_139])).
% 4.08/1.81  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.08/1.81  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.08/1.81  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.08/1.81  tff(c_386, plain, (![A_82, B_83]: (k2_pre_topc(A_82, B_83)=B_83 | ~v4_pre_topc(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.08/1.81  tff(c_396, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_386])).
% 4.08/1.81  tff(c_405, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_396])).
% 4.08/1.81  tff(c_407, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_405])).
% 4.08/1.81  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.08/1.81  tff(c_60, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.08/1.81  tff(c_222, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k3_subset_1(A_70, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.08/1.81  tff(c_233, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_56, c_222])).
% 4.08/1.81  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.08/1.81  tff(c_271, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_233, c_4])).
% 4.08/1.81  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.08/1.81  tff(c_54, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.08/1.81  tff(c_94, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 4.08/1.81  tff(c_141, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_56, c_133])).
% 4.08/1.81  tff(c_518, plain, (![B_96, A_97]: (v4_pre_topc(B_96, A_97) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_97), B_96), A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.08/1.81  tff(c_525, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_141, c_518])).
% 4.08/1.81  tff(c_535, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_94, c_525])).
% 4.08/1.81  tff(c_624, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_535])).
% 4.08/1.81  tff(c_627, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_624])).
% 4.08/1.81  tff(c_631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_627])).
% 4.08/1.81  tff(c_632, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_535])).
% 4.08/1.81  tff(c_633, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_535])).
% 4.08/1.81  tff(c_872, plain, (![B_119, A_120]: (v3_pre_topc(B_119, A_120) | ~v4_pre_topc(B_119, A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~v3_tdlat_3(A_120) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.08/1.81  tff(c_875, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_633, c_872])).
% 4.08/1.81  tff(c_892, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_60, c_632, c_875])).
% 4.08/1.81  tff(c_30, plain, (![B_24, A_22]: (v4_pre_topc(B_24, A_22) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_22), B_24), A_22) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.08/1.81  tff(c_901, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_892, c_30])).
% 4.08/1.81  tff(c_904, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_901])).
% 4.08/1.81  tff(c_906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_904])).
% 4.08/1.81  tff(c_907, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_405])).
% 4.08/1.81  tff(c_913, plain, (![B_121, A_122]: (v1_tops_1(B_121, A_122) | k2_pre_topc(A_122, B_121)!=u1_struct_0(A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.08/1.81  tff(c_923, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_913])).
% 4.08/1.81  tff(c_932, plain, (v1_tops_1('#skF_3', '#skF_2') | u1_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_907, c_923])).
% 4.08/1.81  tff(c_934, plain, (u1_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_932])).
% 4.08/1.81  tff(c_990, plain, (![A_128, B_129]: (k2_pre_topc(A_128, B_129)=u1_struct_0(A_128) | ~v1_tops_1(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.08/1.81  tff(c_1000, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_990])).
% 4.08/1.82  tff(c_1009, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_907, c_1000])).
% 4.08/1.82  tff(c_1010, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_934, c_1009])).
% 4.08/1.82  tff(c_52, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.08/1.82  tff(c_1407, plain, (![B_160, A_161]: (v1_tops_1(B_160, A_161) | ~v3_tex_2(B_160, A_161) | ~v3_pre_topc(B_160, A_161) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.08/1.82  tff(c_1420, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1407])).
% 4.08/1.82  tff(c_1433, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_94, c_52, c_1420])).
% 4.08/1.82  tff(c_1435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1010, c_1433])).
% 4.08/1.82  tff(c_1437, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_932])).
% 4.08/1.82  tff(c_50, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.08/1.82  tff(c_110, plain, (![B_49, A_50]: (~v1_subset_1(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.08/1.82  tff(c_116, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_110])).
% 4.08/1.82  tff(c_123, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_116])).
% 4.08/1.82  tff(c_275, plain, (![A_75, B_76]: (~v1_xboole_0(k3_subset_1(A_75, B_76)) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)) | ~v1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.08/1.82  tff(c_284, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_275])).
% 4.08/1.82  tff(c_292, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_284])).
% 4.08/1.82  tff(c_293, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_123, c_292])).
% 4.08/1.82  tff(c_1439, plain, (~v1_xboole_0(k3_subset_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_293])).
% 4.08/1.82  tff(c_1451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_143, c_1439])).
% 4.08/1.82  tff(c_1453, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 4.08/1.82  tff(c_1452, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 4.08/1.82  tff(c_2448, plain, (![B_253, A_254]: (v3_pre_topc(B_253, A_254) | ~v4_pre_topc(B_253, A_254) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_254))) | ~v3_tdlat_3(A_254) | ~l1_pre_topc(A_254) | ~v2_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.08/1.82  tff(c_2458, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_2448])).
% 4.08/1.82  tff(c_2467, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_60, c_1452, c_2458])).
% 4.08/1.82  tff(c_2469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1453, c_2467])).
% 4.08/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.82  
% 4.08/1.82  Inference rules
% 4.08/1.82  ----------------------
% 4.08/1.82  #Ref     : 0
% 4.08/1.82  #Sup     : 494
% 4.08/1.82  #Fact    : 0
% 4.08/1.82  #Define  : 0
% 4.08/1.82  #Split   : 13
% 4.08/1.82  #Chain   : 0
% 4.08/1.82  #Close   : 0
% 4.08/1.82  
% 4.08/1.82  Ordering : KBO
% 4.08/1.82  
% 4.08/1.82  Simplification rules
% 4.08/1.82  ----------------------
% 4.08/1.82  #Subsume      : 34
% 4.08/1.82  #Demod        : 456
% 4.08/1.82  #Tautology    : 207
% 4.08/1.82  #SimpNegUnit  : 24
% 4.08/1.82  #BackRed      : 10
% 4.08/1.82  
% 4.08/1.82  #Partial instantiations: 0
% 4.08/1.82  #Strategies tried      : 1
% 4.08/1.82  
% 4.08/1.82  Timing (in seconds)
% 4.08/1.82  ----------------------
% 4.08/1.82  Preprocessing        : 0.33
% 4.08/1.82  Parsing              : 0.16
% 4.08/1.82  CNF conversion       : 0.02
% 4.08/1.82  Main loop            : 0.62
% 4.08/1.82  Inferencing          : 0.23
% 4.08/1.82  Reduction            : 0.22
% 4.08/1.82  Demodulation         : 0.16
% 4.08/1.82  BG Simplification    : 0.03
% 4.08/1.82  Subsumption          : 0.08
% 4.08/1.82  Abstraction          : 0.03
% 4.08/1.82  MUC search           : 0.00
% 4.08/1.82  Cooper               : 0.00
% 4.08/1.82  Total                : 0.99
% 4.08/1.82  Index Insertion      : 0.00
% 4.08/1.82  Index Deletion       : 0.00
% 4.08/1.82  Index Matching       : 0.00
% 4.08/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
