%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:26 EST 2020

% Result     : Theorem 6.69s
% Output     : CNFRefutation 7.03s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 233 expanded)
%              Number of leaves         :   42 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  201 ( 711 expanded)
%              Number of equality atoms :   33 (  60 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_152,negated_conjecture,(
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

tff(f_73,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_130,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_154,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [A_39,B_40] : r1_tarski(k4_xboole_0(A_39,B_40),A_39) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,(
    ! [B_40] : k4_xboole_0(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_187,plain,(
    ! [B_51] : k3_xboole_0(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_192,plain,(
    ! [B_51] : k3_xboole_0(B_51,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_2])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_154])).

tff(c_315,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_183])).

tff(c_80,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_73])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_398,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_453,plain,(
    ! [B_71,A_72] :
      ( k4_xboole_0(B_71,A_72) = k3_subset_1(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_22,c_398])).

tff(c_471,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_subset_1(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_80,c_453])).

tff(c_484,plain,(
    ! [A_5] : k3_subset_1(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_471])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1474,plain,(
    ! [A_105,B_106] :
      ( k2_pre_topc(A_105,B_106) = B_106
      | ~ v4_pre_topc(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1484,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1474])).

tff(c_1489,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1484])).

tff(c_1490,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1489])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_406,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_398])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_413,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_6])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_143,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_257,plain,(
    ! [A_55,B_56] :
      ( k3_subset_1(A_55,k3_subset_1(A_55,B_56)) = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_263,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_257])).

tff(c_3282,plain,(
    ! [B_131,A_132] :
      ( v4_pre_topc(B_131,A_132)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_132),B_131),A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3309,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_3282])).

tff(c_3311,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_143,c_3309])).

tff(c_3315,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3311])).

tff(c_3318,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_3315])).

tff(c_3322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_3318])).

tff(c_3323,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3311])).

tff(c_3324,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3311])).

tff(c_4336,plain,(
    ! [B_141,A_142] :
      ( v3_pre_topc(B_141,A_142)
      | ~ v4_pre_topc(B_141,A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ v3_tdlat_3(A_142)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4339,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3324,c_4336])).

tff(c_4352,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_3323,c_4339])).

tff(c_28,plain,(
    ! [B_23,A_21] :
      ( v4_pre_topc(B_23,A_21)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_21),B_23),A_21)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4360,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4352,c_28])).

tff(c_4363,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4360])).

tff(c_4365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1490,c_4363])).

tff(c_4366,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1489])).

tff(c_4565,plain,(
    ! [A_145,B_146] :
      ( k2_pre_topc(A_145,B_146) = u1_struct_0(A_145)
      | ~ v1_tops_1(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4575,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_4565])).

tff(c_4580,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4366,c_4575])).

tff(c_4581,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4580])).

tff(c_50,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_7252,plain,(
    ! [B_179,A_180] :
      ( v1_tops_1(B_179,A_180)
      | ~ v3_tex_2(B_179,A_180)
      | ~ v3_pre_topc(B_179,A_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7265,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_7252])).

tff(c_7274,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_143,c_50,c_7265])).

tff(c_7276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4581,c_7274])).

tff(c_7277,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4580])).

tff(c_48,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_244,plain,(
    ! [B_53,A_54] :
      ( ~ v1_subset_1(B_53,A_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_250,plain,
    ( ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_244])).

tff(c_254,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_250])).

tff(c_1089,plain,(
    ! [A_95,B_96] :
      ( ~ v1_xboole_0(k3_subset_1(A_95,B_96))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95))
      | ~ v1_subset_1(B_96,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1098,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_1089])).

tff(c_1103,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1098])).

tff(c_1104,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_1103])).

tff(c_7281,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7277,c_1104])).

tff(c_7296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_484,c_7281])).

tff(c_7298,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7297,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_11519,plain,(
    ! [B_277,A_278] :
      ( v3_pre_topc(B_277,A_278)
      | ~ v4_pre_topc(B_277,A_278)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ v3_tdlat_3(A_278)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11532,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_11519])).

tff(c_11540,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_7297,c_11532])).

tff(c_11542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7298,c_11540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:25:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.69/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.47  
% 6.69/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.47  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 6.69/2.47  
% 6.69/2.47  %Foreground sorts:
% 6.69/2.47  
% 6.69/2.47  
% 6.69/2.47  %Background operators:
% 6.69/2.47  
% 6.69/2.47  
% 6.69/2.47  %Foreground operators:
% 6.69/2.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.69/2.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.69/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.69/2.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.69/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.69/2.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.69/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.69/2.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.69/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.69/2.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.69/2.47  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 6.69/2.47  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.69/2.47  tff('#skF_2', type, '#skF_2': $i).
% 6.69/2.47  tff('#skF_3', type, '#skF_3': $i).
% 6.69/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.69/2.47  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 6.69/2.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.69/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.69/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.69/2.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.69/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.69/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.69/2.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.69/2.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.69/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.69/2.47  
% 7.03/2.49  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.03/2.49  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.03/2.49  tff(f_30, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.03/2.49  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.03/2.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.03/2.49  tff(f_32, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.03/2.49  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.03/2.49  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.03/2.49  tff(f_152, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 7.03/2.49  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.03/2.49  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.03/2.49  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 7.03/2.49  tff(f_114, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 7.03/2.49  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 7.03/2.49  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 7.03/2.49  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 7.03/2.49  tff(f_101, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 7.03/2.49  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 7.03/2.49  tff(c_154, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.03/2.49  tff(c_73, plain, (![A_39, B_40]: (r1_tarski(k4_xboole_0(A_39, B_40), A_39))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.03/2.49  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.03/2.49  tff(c_81, plain, (![B_40]: (k4_xboole_0(k1_xboole_0, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_10])).
% 7.03/2.49  tff(c_187, plain, (![B_51]: (k3_xboole_0(k1_xboole_0, B_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154, c_81])).
% 7.03/2.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.03/2.49  tff(c_192, plain, (![B_51]: (k3_xboole_0(B_51, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_187, c_2])).
% 7.03/2.49  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.03/2.49  tff(c_183, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_154])).
% 7.03/2.49  tff(c_315, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_183])).
% 7.03/2.49  tff(c_80, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_73])).
% 7.03/2.49  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.03/2.49  tff(c_398, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.03/2.49  tff(c_453, plain, (![B_71, A_72]: (k4_xboole_0(B_71, A_72)=k3_subset_1(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(resolution, [status(thm)], [c_22, c_398])).
% 7.03/2.49  tff(c_471, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_subset_1(A_5, A_5))), inference(resolution, [status(thm)], [c_80, c_453])).
% 7.03/2.49  tff(c_484, plain, (![A_5]: (k3_subset_1(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_471])).
% 7.03/2.49  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.03/2.49  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.03/2.49  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.03/2.49  tff(c_1474, plain, (![A_105, B_106]: (k2_pre_topc(A_105, B_106)=B_106 | ~v4_pre_topc(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.03/2.49  tff(c_1484, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1474])).
% 7.03/2.49  tff(c_1489, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1484])).
% 7.03/2.49  tff(c_1490, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1489])).
% 7.03/2.49  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.03/2.49  tff(c_58, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.03/2.49  tff(c_406, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_54, c_398])).
% 7.03/2.49  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.03/2.49  tff(c_413, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_6])).
% 7.03/2.49  tff(c_52, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.03/2.49  tff(c_143, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 7.03/2.49  tff(c_257, plain, (![A_55, B_56]: (k3_subset_1(A_55, k3_subset_1(A_55, B_56))=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.03/2.49  tff(c_263, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_54, c_257])).
% 7.03/2.49  tff(c_3282, plain, (![B_131, A_132]: (v4_pre_topc(B_131, A_132) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_132), B_131), A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.03/2.49  tff(c_3309, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_263, c_3282])).
% 7.03/2.49  tff(c_3311, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_143, c_3309])).
% 7.03/2.49  tff(c_3315, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3311])).
% 7.03/2.49  tff(c_3318, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_3315])).
% 7.03/2.49  tff(c_3322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_413, c_3318])).
% 7.03/2.49  tff(c_3323, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_3311])).
% 7.03/2.49  tff(c_3324, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3311])).
% 7.03/2.49  tff(c_4336, plain, (![B_141, A_142]: (v3_pre_topc(B_141, A_142) | ~v4_pre_topc(B_141, A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~v3_tdlat_3(A_142) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.03/2.49  tff(c_4339, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3324, c_4336])).
% 7.03/2.49  tff(c_4352, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_3323, c_4339])).
% 7.03/2.49  tff(c_28, plain, (![B_23, A_21]: (v4_pre_topc(B_23, A_21) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_21), B_23), A_21) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.03/2.49  tff(c_4360, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4352, c_28])).
% 7.03/2.49  tff(c_4363, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4360])).
% 7.03/2.49  tff(c_4365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1490, c_4363])).
% 7.03/2.49  tff(c_4366, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1489])).
% 7.03/2.49  tff(c_4565, plain, (![A_145, B_146]: (k2_pre_topc(A_145, B_146)=u1_struct_0(A_145) | ~v1_tops_1(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.03/2.49  tff(c_4575, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_4565])).
% 7.03/2.49  tff(c_4580, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4366, c_4575])).
% 7.03/2.49  tff(c_4581, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_4580])).
% 7.03/2.49  tff(c_50, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.03/2.49  tff(c_7252, plain, (![B_179, A_180]: (v1_tops_1(B_179, A_180) | ~v3_tex_2(B_179, A_180) | ~v3_pre_topc(B_179, A_180) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.03/2.49  tff(c_7265, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_7252])).
% 7.03/2.49  tff(c_7274, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_143, c_50, c_7265])).
% 7.03/2.49  tff(c_7276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4581, c_7274])).
% 7.03/2.49  tff(c_7277, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_4580])).
% 7.03/2.49  tff(c_48, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.03/2.49  tff(c_244, plain, (![B_53, A_54]: (~v1_subset_1(B_53, A_54) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.03/2.49  tff(c_250, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_244])).
% 7.03/2.49  tff(c_254, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_250])).
% 7.03/2.49  tff(c_1089, plain, (![A_95, B_96]: (~v1_xboole_0(k3_subset_1(A_95, B_96)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)) | ~v1_subset_1(B_96, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.03/2.49  tff(c_1098, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_1089])).
% 7.03/2.49  tff(c_1103, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1098])).
% 7.03/2.49  tff(c_1104, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_254, c_1103])).
% 7.03/2.49  tff(c_7281, plain, (~v1_xboole_0(k3_subset_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7277, c_1104])).
% 7.03/2.49  tff(c_7296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_484, c_7281])).
% 7.03/2.49  tff(c_7298, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 7.03/2.49  tff(c_7297, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 7.03/2.49  tff(c_11519, plain, (![B_277, A_278]: (v3_pre_topc(B_277, A_278) | ~v4_pre_topc(B_277, A_278) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_278))) | ~v3_tdlat_3(A_278) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.03/2.49  tff(c_11532, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_11519])).
% 7.03/2.49  tff(c_11540, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_7297, c_11532])).
% 7.03/2.49  tff(c_11542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7298, c_11540])).
% 7.03/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.03/2.49  
% 7.03/2.49  Inference rules
% 7.03/2.49  ----------------------
% 7.03/2.49  #Ref     : 0
% 7.03/2.49  #Sup     : 2774
% 7.03/2.49  #Fact    : 0
% 7.03/2.49  #Define  : 0
% 7.03/2.49  #Split   : 12
% 7.03/2.49  #Chain   : 0
% 7.03/2.49  #Close   : 0
% 7.03/2.49  
% 7.03/2.49  Ordering : KBO
% 7.03/2.49  
% 7.03/2.49  Simplification rules
% 7.03/2.49  ----------------------
% 7.03/2.49  #Subsume      : 171
% 7.03/2.49  #Demod        : 4406
% 7.03/2.49  #Tautology    : 2344
% 7.03/2.49  #SimpNegUnit  : 15
% 7.03/2.49  #BackRed      : 16
% 7.03/2.49  
% 7.03/2.49  #Partial instantiations: 0
% 7.03/2.49  #Strategies tried      : 1
% 7.03/2.49  
% 7.03/2.49  Timing (in seconds)
% 7.03/2.49  ----------------------
% 7.03/2.49  Preprocessing        : 0.35
% 7.03/2.49  Parsing              : 0.19
% 7.03/2.49  CNF conversion       : 0.02
% 7.03/2.49  Main loop            : 1.35
% 7.03/2.49  Inferencing          : 0.38
% 7.03/2.49  Reduction            : 0.71
% 7.03/2.49  Demodulation         : 0.60
% 7.03/2.49  BG Simplification    : 0.04
% 7.03/2.49  Subsumption          : 0.15
% 7.03/2.49  Abstraction          : 0.07
% 7.03/2.49  MUC search           : 0.00
% 7.03/2.49  Cooper               : 0.00
% 7.03/2.49  Total                : 1.74
% 7.03/2.49  Index Insertion      : 0.00
% 7.03/2.49  Index Deletion       : 0.00
% 7.03/2.49  Index Matching       : 0.00
% 7.03/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
