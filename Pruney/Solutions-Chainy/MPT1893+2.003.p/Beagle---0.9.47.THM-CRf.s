%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:26 EST 2020

% Result     : Theorem 5.85s
% Output     : CNFRefutation 6.27s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 256 expanded)
%              Number of leaves         :   42 ( 104 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 ( 843 expanded)
%              Number of equality atoms :   34 (  73 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_92,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [A_39,B_40] : r1_tarski(k3_xboole_0(A_39,B_40),A_39) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,(
    ! [B_40] : k3_xboole_0(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_10])).

tff(c_108,plain,(
    ! [B_42] : k3_xboole_0(B_42,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_76])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_191,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_206,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_191])).

tff(c_209,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_206])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_922,plain,(
    ! [A_84,B_85] :
      ( k2_pre_topc(A_84,B_85) = B_85
      | ~ v4_pre_topc(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_932,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_922])).

tff(c_937,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_932])).

tff(c_938,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_937])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k3_subset_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_181,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_330,plain,(
    ! [A_60,B_61] :
      ( k3_subset_1(A_60,k3_subset_1(A_60,B_61)) = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_336,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_52,c_330])).

tff(c_1588,plain,(
    ! [B_101,A_102] :
      ( v4_pre_topc(B_101,A_102)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_102),B_101),A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1595,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_1588])).

tff(c_1597,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_181,c_1595])).

tff(c_1598,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1597])).

tff(c_1601,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_1598])).

tff(c_1605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1601])).

tff(c_1606,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1597])).

tff(c_1607,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1597])).

tff(c_2419,plain,(
    ! [B_115,A_116] :
      ( v3_pre_topc(B_115,A_116)
      | ~ v4_pre_topc(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ v3_tdlat_3(A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2422,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1607,c_2419])).

tff(c_2435,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_56,c_1606,c_2422])).

tff(c_26,plain,(
    ! [B_23,A_21] :
      ( v4_pre_topc(B_23,A_21)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_21),B_23),A_21)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2443,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2435,c_26])).

tff(c_2446,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2443])).

tff(c_2448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_938,c_2446])).

tff(c_2449,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_937])).

tff(c_2550,plain,(
    ! [B_122,A_123] :
      ( v1_tops_1(B_122,A_123)
      | k2_pre_topc(A_123,B_122) != u1_struct_0(A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2560,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2550])).

tff(c_2565,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | u1_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2449,c_2560])).

tff(c_2620,plain,(
    u1_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2565])).

tff(c_2749,plain,(
    ! [A_124,B_125] :
      ( k2_pre_topc(A_124,B_125) = u1_struct_0(A_124)
      | ~ v1_tops_1(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2759,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2749])).

tff(c_2764,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2449,c_2759])).

tff(c_2765,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2620,c_2764])).

tff(c_48,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3965,plain,(
    ! [B_153,A_154] :
      ( v1_tops_1(B_153,A_154)
      | ~ v3_tex_2(B_153,A_154)
      | ~ v3_pre_topc(B_153,A_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3978,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_3965])).

tff(c_3987,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_181,c_48,c_3978])).

tff(c_3989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2765,c_3987])).

tff(c_3991,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2565])).

tff(c_3998,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3991,c_52])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k3_subset_1(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4036,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_subset_1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3998,c_14])).

tff(c_4047,plain,(
    k3_subset_1('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_4036])).

tff(c_46,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_272,plain,(
    ! [B_51,A_52] :
      ( ~ v1_subset_1(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_275,plain,
    ( ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_272])).

tff(c_278,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_275])).

tff(c_575,plain,(
    ! [A_74,B_75] :
      ( ~ v1_xboole_0(k3_subset_1(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74))
      | ~ v1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_584,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_575])).

tff(c_589,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_584])).

tff(c_590,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_589])).

tff(c_3994,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3991,c_590])).

tff(c_4051,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4047,c_3994])).

tff(c_4054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4051])).

tff(c_4056,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4055,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6234,plain,(
    ! [B_225,A_226] :
      ( v3_pre_topc(B_225,A_226)
      | ~ v4_pre_topc(B_225,A_226)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ v3_tdlat_3(A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6244,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_6234])).

tff(c_6249,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_56,c_4055,c_6244])).

tff(c_6251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4056,c_6249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:29:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.85/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.20  
% 5.85/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.21  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 5.85/2.21  
% 5.85/2.21  %Foreground sorts:
% 5.85/2.21  
% 5.85/2.21  
% 5.85/2.21  %Background operators:
% 5.85/2.21  
% 5.85/2.21  
% 5.85/2.21  %Foreground operators:
% 5.85/2.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.85/2.21  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.85/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.85/2.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.85/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.85/2.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.85/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.85/2.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.85/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.85/2.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.85/2.21  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.85/2.21  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.85/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.85/2.21  tff('#skF_3', type, '#skF_3': $i).
% 5.85/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.85/2.21  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 5.85/2.21  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.85/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.85/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.85/2.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.85/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.85/2.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.85/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.85/2.21  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.85/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.85/2.21  
% 6.27/2.22  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.27/2.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.27/2.22  tff(f_30, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.27/2.22  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.27/2.22  tff(f_32, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.27/2.22  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.27/2.22  tff(f_152, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 6.27/2.22  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.27/2.22  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.27/2.22  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.27/2.22  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 6.27/2.22  tff(f_114, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 6.27/2.22  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 6.27/2.22  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 6.27/2.22  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.27/2.22  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 6.27/2.22  tff(f_101, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tex_2)).
% 6.27/2.22  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 6.27/2.22  tff(c_92, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.27/2.22  tff(c_71, plain, (![A_39, B_40]: (r1_tarski(k3_xboole_0(A_39, B_40), A_39))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.27/2.22  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.27/2.22  tff(c_76, plain, (![B_40]: (k3_xboole_0(k1_xboole_0, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_71, c_10])).
% 6.27/2.22  tff(c_108, plain, (![B_42]: (k3_xboole_0(B_42, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_76])).
% 6.27/2.22  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.27/2.22  tff(c_191, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.27/2.22  tff(c_206, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_191])).
% 6.27/2.22  tff(c_209, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_206])).
% 6.27/2.22  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.27/2.22  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.27/2.22  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.27/2.22  tff(c_922, plain, (![A_84, B_85]: (k2_pre_topc(A_84, B_85)=B_85 | ~v4_pre_topc(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.27/2.22  tff(c_932, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_922])).
% 6.27/2.22  tff(c_937, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_932])).
% 6.27/2.22  tff(c_938, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_937])).
% 6.27/2.22  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.27/2.22  tff(c_56, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.27/2.22  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k3_subset_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.27/2.22  tff(c_50, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.27/2.22  tff(c_181, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 6.27/2.22  tff(c_330, plain, (![A_60, B_61]: (k3_subset_1(A_60, k3_subset_1(A_60, B_61))=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.27/2.22  tff(c_336, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_52, c_330])).
% 6.27/2.22  tff(c_1588, plain, (![B_101, A_102]: (v4_pre_topc(B_101, A_102) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_102), B_101), A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.27/2.22  tff(c_1595, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_336, c_1588])).
% 6.27/2.22  tff(c_1597, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_181, c_1595])).
% 6.27/2.22  tff(c_1598, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1597])).
% 6.27/2.22  tff(c_1601, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_1598])).
% 6.27/2.22  tff(c_1605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1601])).
% 6.27/2.22  tff(c_1606, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1597])).
% 6.27/2.22  tff(c_1607, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1597])).
% 6.27/2.22  tff(c_2419, plain, (![B_115, A_116]: (v3_pre_topc(B_115, A_116) | ~v4_pre_topc(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~v3_tdlat_3(A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.27/2.22  tff(c_2422, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1607, c_2419])).
% 6.27/2.22  tff(c_2435, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_56, c_1606, c_2422])).
% 6.27/2.22  tff(c_26, plain, (![B_23, A_21]: (v4_pre_topc(B_23, A_21) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_21), B_23), A_21) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.27/2.22  tff(c_2443, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2435, c_26])).
% 6.27/2.22  tff(c_2446, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2443])).
% 6.27/2.22  tff(c_2448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_938, c_2446])).
% 6.27/2.22  tff(c_2449, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_937])).
% 6.27/2.22  tff(c_2550, plain, (![B_122, A_123]: (v1_tops_1(B_122, A_123) | k2_pre_topc(A_123, B_122)!=u1_struct_0(A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.27/2.22  tff(c_2560, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2550])).
% 6.27/2.22  tff(c_2565, plain, (v1_tops_1('#skF_3', '#skF_2') | u1_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2449, c_2560])).
% 6.27/2.22  tff(c_2620, plain, (u1_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_2565])).
% 6.27/2.22  tff(c_2749, plain, (![A_124, B_125]: (k2_pre_topc(A_124, B_125)=u1_struct_0(A_124) | ~v1_tops_1(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.27/2.22  tff(c_2759, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2749])).
% 6.27/2.22  tff(c_2764, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2449, c_2759])).
% 6.27/2.22  tff(c_2765, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2620, c_2764])).
% 6.27/2.22  tff(c_48, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.27/2.22  tff(c_3965, plain, (![B_153, A_154]: (v1_tops_1(B_153, A_154) | ~v3_tex_2(B_153, A_154) | ~v3_pre_topc(B_153, A_154) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.27/2.22  tff(c_3978, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_3965])).
% 6.27/2.22  tff(c_3987, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_181, c_48, c_3978])).
% 6.27/2.22  tff(c_3989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2765, c_3987])).
% 6.27/2.22  tff(c_3991, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2565])).
% 6.27/2.22  tff(c_3998, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3991, c_52])).
% 6.27/2.22  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=k3_subset_1(A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.27/2.22  tff(c_4036, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_subset_1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3998, c_14])).
% 6.27/2.22  tff(c_4047, plain, (k3_subset_1('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_4036])).
% 6.27/2.22  tff(c_46, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.27/2.22  tff(c_272, plain, (![B_51, A_52]: (~v1_subset_1(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.27/2.22  tff(c_275, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_272])).
% 6.27/2.22  tff(c_278, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_275])).
% 6.27/2.22  tff(c_575, plain, (![A_74, B_75]: (~v1_xboole_0(k3_subset_1(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)) | ~v1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.27/2.22  tff(c_584, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_575])).
% 6.27/2.22  tff(c_589, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_584])).
% 6.27/2.22  tff(c_590, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_278, c_589])).
% 6.27/2.22  tff(c_3994, plain, (~v1_xboole_0(k3_subset_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3991, c_590])).
% 6.27/2.22  tff(c_4051, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4047, c_3994])).
% 6.27/2.22  tff(c_4054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4051])).
% 6.27/2.22  tff(c_4056, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 6.27/2.22  tff(c_4055, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 6.27/2.22  tff(c_6234, plain, (![B_225, A_226]: (v3_pre_topc(B_225, A_226) | ~v4_pre_topc(B_225, A_226) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_226))) | ~v3_tdlat_3(A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.27/2.22  tff(c_6244, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_6234])).
% 6.27/2.22  tff(c_6249, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_56, c_4055, c_6244])).
% 6.27/2.22  tff(c_6251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4056, c_6249])).
% 6.27/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.22  
% 6.27/2.22  Inference rules
% 6.27/2.22  ----------------------
% 6.27/2.22  #Ref     : 0
% 6.27/2.22  #Sup     : 1497
% 6.27/2.22  #Fact    : 0
% 6.27/2.22  #Define  : 0
% 6.27/2.22  #Split   : 12
% 6.27/2.22  #Chain   : 0
% 6.27/2.22  #Close   : 0
% 6.27/2.22  
% 6.27/2.22  Ordering : KBO
% 6.27/2.22  
% 6.27/2.22  Simplification rules
% 6.27/2.22  ----------------------
% 6.27/2.22  #Subsume      : 28
% 6.27/2.22  #Demod        : 3341
% 6.27/2.22  #Tautology    : 1180
% 6.27/2.22  #SimpNegUnit  : 16
% 6.27/2.22  #BackRed      : 15
% 6.27/2.22  
% 6.27/2.22  #Partial instantiations: 0
% 6.27/2.22  #Strategies tried      : 1
% 6.27/2.22  
% 6.27/2.22  Timing (in seconds)
% 6.27/2.22  ----------------------
% 6.27/2.23  Preprocessing        : 0.34
% 6.27/2.23  Parsing              : 0.18
% 6.27/2.23  CNF conversion       : 0.02
% 6.27/2.23  Main loop            : 1.12
% 6.27/2.23  Inferencing          : 0.29
% 6.27/2.23  Reduction            : 0.59
% 6.27/2.23  Demodulation         : 0.51
% 6.27/2.23  BG Simplification    : 0.03
% 6.27/2.23  Subsumption          : 0.14
% 6.27/2.23  Abstraction          : 0.05
% 6.27/2.23  MUC search           : 0.00
% 6.27/2.23  Cooper               : 0.00
% 6.27/2.23  Total                : 1.50
% 6.27/2.23  Index Insertion      : 0.00
% 6.27/2.23  Index Deletion       : 0.00
% 6.27/2.23  Index Matching       : 0.00
% 6.27/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
