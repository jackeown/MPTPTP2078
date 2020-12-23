%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:48 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 170 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 507 expanded)
%              Number of equality atoms :   38 ( 120 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( v3_pre_topc(D,B)
                       => k1_tops_1(B,D) = D )
                      & ( k1_tops_1(A,C) = C
                       => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_36,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_280,plain,(
    ! [A_51,B_52] :
      ( v3_pre_topc(k1_tops_1(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_287,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_280])).

tff(c_294,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_52,c_287])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_294])).

tff(c_298,plain,(
    k1_tops_1('#skF_1','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_304,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_38])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_305,plain,(
    ! [A_55,B_56] :
      ( k3_subset_1(A_55,k3_subset_1(A_55,B_56)) = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_313,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_305])).

tff(c_297,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_17),B_19),A_17)
      | ~ v3_pre_topc(B_19,A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_319,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_330,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_319])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_339,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_2])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_460,plain,(
    ! [A_65,B_66] :
      ( k2_pre_topc(A_65,B_66) = B_66
      | ~ v4_pre_topc(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_643,plain,(
    ! [A_79,A_80] :
      ( k2_pre_topc(A_79,A_80) = A_80
      | ~ v4_pre_topc(A_80,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ r1_tarski(A_80,u1_struct_0(A_79)) ) ),
    inference(resolution,[status(thm)],[c_10,c_460])).

tff(c_661,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_339,c_643])).

tff(c_680,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_661])).

tff(c_1041,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_680])).

tff(c_1044,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1041])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_297,c_1044])).

tff(c_1049,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_680])).

tff(c_16,plain,(
    ! [A_12,B_14] :
      ( k3_subset_1(u1_struct_0(A_12),k2_pre_topc(A_12,k3_subset_1(u1_struct_0(A_12),B_14))) = k1_tops_1(A_12,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1098,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_16])).

tff(c_1102,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_313,c_1098])).

tff(c_1104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_1102])).

tff(c_1106,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1110,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_34])).

tff(c_1124,plain,(
    ! [A_101,B_102] :
      ( k3_subset_1(A_101,k3_subset_1(A_101,B_102)) = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1132,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_1124])).

tff(c_1105,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1191,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k3_subset_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1202,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1191])).

tff(c_1207,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1202,c_2])).

tff(c_1218,plain,(
    ! [A_107,B_108] :
      ( k2_pre_topc(A_107,B_108) = B_108
      | ~ v4_pre_topc(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1438,plain,(
    ! [A_123,A_124] :
      ( k2_pre_topc(A_123,A_124) = A_124
      | ~ v4_pre_topc(A_124,A_123)
      | ~ l1_pre_topc(A_123)
      | ~ r1_tarski(A_124,u1_struct_0(A_123)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1218])).

tff(c_1456,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1207,c_1438])).

tff(c_1475,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1456])).

tff(c_1854,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1475])).

tff(c_1857,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1854])).

tff(c_1861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_1105,c_1857])).

tff(c_1862,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1475])).

tff(c_1873,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_16])).

tff(c_1877,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_1132,c_1873])).

tff(c_1879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1110,c_1877])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.56  
% 3.54/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.56  %$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.54/1.56  
% 3.54/1.56  %Foreground sorts:
% 3.54/1.56  
% 3.54/1.56  
% 3.54/1.56  %Background operators:
% 3.54/1.56  
% 3.54/1.56  
% 3.54/1.56  %Foreground operators:
% 3.54/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.54/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.54/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.54/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.54/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.54/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.54/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.54/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.56  
% 3.54/1.58  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 3.54/1.58  tff(f_69, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.54/1.58  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.54/1.58  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 3.54/1.58  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.54/1.58  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.54/1.58  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.54/1.58  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.54/1.58  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.54/1.58  tff(c_36, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_42, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.54/1.58  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_40, plain, (v3_pre_topc('#skF_4', '#skF_2') | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_52, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_40])).
% 3.54/1.58  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_280, plain, (![A_51, B_52]: (v3_pre_topc(k1_tops_1(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.54/1.58  tff(c_287, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_280])).
% 3.54/1.58  tff(c_294, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_52, c_287])).
% 3.54/1.58  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_294])).
% 3.54/1.58  tff(c_298, plain, (k1_tops_1('#skF_1', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 3.54/1.58  tff(c_38, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_304, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_298, c_38])).
% 3.54/1.58  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_305, plain, (![A_55, B_56]: (k3_subset_1(A_55, k3_subset_1(A_55, B_56))=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.58  tff(c_313, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_24, c_305])).
% 3.54/1.58  tff(c_297, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 3.54/1.58  tff(c_22, plain, (![A_17, B_19]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_17), B_19), A_17) | ~v3_pre_topc(B_19, A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.54/1.58  tff(c_319, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.58  tff(c_330, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_24, c_319])).
% 3.54/1.58  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.58  tff(c_339, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_330, c_2])).
% 3.54/1.58  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.58  tff(c_460, plain, (![A_65, B_66]: (k2_pre_topc(A_65, B_66)=B_66 | ~v4_pre_topc(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.58  tff(c_643, plain, (![A_79, A_80]: (k2_pre_topc(A_79, A_80)=A_80 | ~v4_pre_topc(A_80, A_79) | ~l1_pre_topc(A_79) | ~r1_tarski(A_80, u1_struct_0(A_79)))), inference(resolution, [status(thm)], [c_10, c_460])).
% 3.54/1.58  tff(c_661, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_339, c_643])).
% 3.54/1.58  tff(c_680, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_661])).
% 3.54/1.58  tff(c_1041, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_680])).
% 3.54/1.58  tff(c_1044, plain, (~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1041])).
% 3.54/1.58  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_297, c_1044])).
% 3.54/1.58  tff(c_1049, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_680])).
% 3.54/1.58  tff(c_16, plain, (![A_12, B_14]: (k3_subset_1(u1_struct_0(A_12), k2_pre_topc(A_12, k3_subset_1(u1_struct_0(A_12), B_14)))=k1_tops_1(A_12, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.58  tff(c_1098, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_16])).
% 3.54/1.58  tff(c_1102, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_313, c_1098])).
% 3.54/1.58  tff(c_1104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_304, c_1102])).
% 3.54/1.58  tff(c_1106, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.54/1.58  tff(c_34, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.54/1.58  tff(c_1110, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_34])).
% 3.54/1.58  tff(c_1124, plain, (![A_101, B_102]: (k3_subset_1(A_101, k3_subset_1(A_101, B_102))=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.58  tff(c_1132, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_24, c_1124])).
% 3.54/1.58  tff(c_1105, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 3.54/1.58  tff(c_1191, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k3_subset_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.58  tff(c_1202, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_24, c_1191])).
% 3.54/1.58  tff(c_1207, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1202, c_2])).
% 3.54/1.58  tff(c_1218, plain, (![A_107, B_108]: (k2_pre_topc(A_107, B_108)=B_108 | ~v4_pre_topc(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.54/1.58  tff(c_1438, plain, (![A_123, A_124]: (k2_pre_topc(A_123, A_124)=A_124 | ~v4_pre_topc(A_124, A_123) | ~l1_pre_topc(A_123) | ~r1_tarski(A_124, u1_struct_0(A_123)))), inference(resolution, [status(thm)], [c_10, c_1218])).
% 3.54/1.58  tff(c_1456, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1207, c_1438])).
% 3.54/1.58  tff(c_1475, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1456])).
% 3.54/1.58  tff(c_1854, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1475])).
% 3.54/1.58  tff(c_1857, plain, (~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1854])).
% 3.54/1.58  tff(c_1861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_1105, c_1857])).
% 3.54/1.58  tff(c_1862, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_1475])).
% 3.54/1.58  tff(c_1873, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1862, c_16])).
% 3.54/1.58  tff(c_1877, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_1132, c_1873])).
% 3.54/1.58  tff(c_1879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1110, c_1877])).
% 3.54/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  Inference rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Ref     : 0
% 3.54/1.58  #Sup     : 409
% 3.54/1.58  #Fact    : 0
% 3.54/1.58  #Define  : 0
% 3.54/1.58  #Split   : 18
% 3.54/1.58  #Chain   : 0
% 3.54/1.58  #Close   : 0
% 3.54/1.58  
% 3.54/1.58  Ordering : KBO
% 3.54/1.58  
% 3.54/1.58  Simplification rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Subsume      : 24
% 3.54/1.58  #Demod        : 377
% 3.54/1.58  #Tautology    : 215
% 3.54/1.58  #SimpNegUnit  : 17
% 3.54/1.58  #BackRed      : 1
% 3.54/1.58  
% 3.54/1.58  #Partial instantiations: 0
% 3.54/1.58  #Strategies tried      : 1
% 3.54/1.58  
% 3.54/1.58  Timing (in seconds)
% 3.54/1.58  ----------------------
% 3.54/1.58  Preprocessing        : 0.31
% 3.54/1.58  Parsing              : 0.17
% 3.54/1.58  CNF conversion       : 0.02
% 3.54/1.58  Main loop            : 0.49
% 3.54/1.58  Inferencing          : 0.18
% 3.54/1.58  Reduction            : 0.18
% 3.54/1.58  Demodulation         : 0.14
% 3.54/1.58  BG Simplification    : 0.02
% 3.54/1.58  Subsumption          : 0.06
% 3.54/1.58  Abstraction          : 0.03
% 3.54/1.58  MUC search           : 0.00
% 3.54/1.58  Cooper               : 0.00
% 3.54/1.58  Total                : 0.84
% 3.54/1.58  Index Insertion      : 0.00
% 3.54/1.58  Index Deletion       : 0.00
% 3.54/1.58  Index Matching       : 0.00
% 3.54/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
