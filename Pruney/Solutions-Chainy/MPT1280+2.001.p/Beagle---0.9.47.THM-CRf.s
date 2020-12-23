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
% DateTime   : Thu Dec  3 10:22:12 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 861 expanded)
%              Number of leaves         :   25 ( 301 expanded)
%              Depth                    :   17
%              Number of atoms          :  207 (2080 expanded)
%              Number of equality atoms :   53 ( 512 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

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

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_26,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_9,B_11] :
      ( k3_subset_1(u1_struct_0(A_9),k2_pre_topc(A_9,k3_subset_1(u1_struct_0(A_9),B_11))) = k1_tops_1(A_9,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_134,plain,(
    ! [A_43,B_44] :
      ( k2_pre_topc(A_43,k1_tops_1(A_43,B_44)) = B_44
      | ~ v5_tops_1(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_143,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_149,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_143])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_tops_1(A_20,k2_pre_topc(A_20,B_22)),k2_tops_1(A_20,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_155,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_24])).

tff(c_165,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_155])).

tff(c_169,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_173,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_169])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_173])).

tff(c_178,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_27,B_28] :
      ( k3_subset_1(A_27,k3_subset_1(A_27,B_28)) = B_28
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_216,plain,(
    ! [A_45,B_46] :
      ( k3_subset_1(u1_struct_0(A_45),k2_pre_topc(A_45,k3_subset_1(u1_struct_0(A_45),B_46))) = k1_tops_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_244,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_216])).

tff(c_250,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_244])).

tff(c_261,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_264,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_261])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_264])).

tff(c_270,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_762,plain,(
    ! [A_57,B_58] :
      ( k2_pre_topc(A_57,k1_tops_1(A_57,k2_pre_topc(A_57,B_58))) = k2_pre_topc(A_57,B_58)
      | ~ v5_tops_1(k2_pre_topc(A_57,B_58),A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_12,c_134])).

tff(c_776,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ v5_tops_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_270,c_762])).

tff(c_808,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ v5_tops_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_776])).

tff(c_820,plain,(
    ~ v5_tops_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_808])).

tff(c_179,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,B_6)) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_10])).

tff(c_237,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_216])).

tff(c_248,plain,
    ( k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_149,c_237])).

tff(c_965,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_969,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_965])).

tff(c_973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_969])).

tff(c_975,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_974,plain,(
    k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_16,plain,(
    ! [B_14,A_12] :
      ( v5_tops_1(B_14,A_12)
      | k2_pre_topc(A_12,k1_tops_1(A_12,B_14)) != B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1008,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) != k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_16])).

tff(c_1019,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) != k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_975,c_1008])).

tff(c_1023,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) != k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1019])).

tff(c_1175,plain,(
    ! [A_67,B_68] :
      ( k3_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,k1_tops_1(A_67,B_68))) = k1_tops_1(A_67,k2_pre_topc(A_67,k3_subset_1(u1_struct_0(A_67),B_68)))
      | ~ m1_subset_1(k2_pre_topc(A_67,k3_subset_1(u1_struct_0(A_67),B_68)),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_14])).

tff(c_1205,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_1175])).

tff(c_1230,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_975,c_32,c_30,c_149,c_974,c_149,c_192,c_1205])).

tff(c_62,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_pre_topc(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_33,B_34] :
      ( k3_subset_1(u1_struct_0(A_33),k3_subset_1(u1_struct_0(A_33),k2_pre_topc(A_33,B_34))) = k2_pre_topc(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_62,c_10])).

tff(c_1249,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_65])).

tff(c_1276,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_270,c_1249])).

tff(c_1278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1023,c_1276])).

tff(c_1280,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1019])).

tff(c_1279,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1019])).

tff(c_1281,plain,(
    v5_tops_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_1279])).

tff(c_1287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_820,c_1281])).

tff(c_1288,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_808])).

tff(c_1304,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_12])).

tff(c_1317,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1304])).

tff(c_1463,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1317])).

tff(c_1467,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1463])).

tff(c_1470,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1467])).

tff(c_1473,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1470])).

tff(c_1477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_270,c_1473])).

tff(c_1478,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1317])).

tff(c_1502,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_1478,c_10])).

tff(c_1605,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1502])).

tff(c_1626,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1605])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( k2_tops_1(A_17,k3_subset_1(u1_struct_0(A_17),B_19)) = k2_tops_1(A_17,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_183,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_179,c_22])).

tff(c_191,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_183])).

tff(c_1627,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_191])).

tff(c_108,plain,(
    ! [A_39,B_40] :
      ( k2_tops_1(A_39,k3_subset_1(u1_struct_0(A_39),B_40)) = k2_tops_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_117,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_123,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_117])).

tff(c_127,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_24])).

tff(c_131,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_127])).

tff(c_394,plain,(
    r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_131])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_397,plain,
    ( k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) ),
    inference(resolution,[status(thm)],[c_394,c_2])).

tff(c_634,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_1740,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1627,c_634])).

tff(c_1744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_1740])).

tff(c_1745,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_1755,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_24])).

tff(c_1761,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1755])).

tff(c_2258,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1761])).

tff(c_2261,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_2258])).

tff(c_2265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_270,c_2261])).

tff(c_2267,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1761])).

tff(c_2275,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2267,c_22])).

tff(c_2289,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1745,c_2275])).

tff(c_2411,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2289])).

tff(c_2423,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2411])).

tff(c_2425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_2423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.83  
% 4.45/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.84  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.45/1.84  
% 4.45/1.84  %Foreground sorts:
% 4.45/1.84  
% 4.45/1.84  
% 4.45/1.84  %Background operators:
% 4.45/1.84  
% 4.45/1.84  
% 4.45/1.84  %Foreground operators:
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.84  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.45/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.45/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.84  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.45/1.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.45/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.84  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.45/1.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.45/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.84  
% 4.45/1.85  tff(f_91, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 4.45/1.85  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 4.45/1.85  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.45/1.85  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 4.45/1.85  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 4.45/1.85  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.45/1.85  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.45/1.85  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.45/1.85  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 4.45/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.45/1.85  tff(c_26, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.45/1.85  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.45/1.85  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.45/1.85  tff(c_14, plain, (![A_9, B_11]: (k3_subset_1(u1_struct_0(A_9), k2_pre_topc(A_9, k3_subset_1(u1_struct_0(A_9), B_11)))=k1_tops_1(A_9, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.45/1.85  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(k1_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.45/1.85  tff(c_28, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.45/1.85  tff(c_134, plain, (![A_43, B_44]: (k2_pre_topc(A_43, k1_tops_1(A_43, B_44))=B_44 | ~v5_tops_1(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.45/1.85  tff(c_143, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_134])).
% 4.45/1.85  tff(c_149, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_143])).
% 4.45/1.85  tff(c_24, plain, (![A_20, B_22]: (r1_tarski(k2_tops_1(A_20, k2_pre_topc(A_20, B_22)), k2_tops_1(A_20, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.45/1.85  tff(c_155, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_149, c_24])).
% 4.45/1.85  tff(c_165, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_155])).
% 4.45/1.85  tff(c_169, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_165])).
% 4.45/1.85  tff(c_173, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_169])).
% 4.45/1.85  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_173])).
% 4.45/1.85  tff(c_178, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_165])).
% 4.45/1.85  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.45/1.85  tff(c_42, plain, (![A_27, B_28]: (k3_subset_1(A_27, k3_subset_1(A_27, B_28))=B_28 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.45/1.85  tff(c_45, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_42])).
% 4.45/1.85  tff(c_216, plain, (![A_45, B_46]: (k3_subset_1(u1_struct_0(A_45), k2_pre_topc(A_45, k3_subset_1(u1_struct_0(A_45), B_46)))=k1_tops_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.45/1.85  tff(c_244, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45, c_216])).
% 4.45/1.85  tff(c_250, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_244])).
% 4.45/1.85  tff(c_261, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_250])).
% 4.45/1.85  tff(c_264, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_261])).
% 4.45/1.85  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_264])).
% 4.45/1.85  tff(c_270, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_250])).
% 4.45/1.85  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.45/1.85  tff(c_762, plain, (![A_57, B_58]: (k2_pre_topc(A_57, k1_tops_1(A_57, k2_pre_topc(A_57, B_58)))=k2_pre_topc(A_57, B_58) | ~v5_tops_1(k2_pre_topc(A_57, B_58), A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_12, c_134])).
% 4.45/1.85  tff(c_776, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~v5_tops_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_270, c_762])).
% 4.45/1.85  tff(c_808, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~v5_tops_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_776])).
% 4.45/1.85  tff(c_820, plain, (~v5_tops_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_808])).
% 4.45/1.85  tff(c_179, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_165])).
% 4.45/1.85  tff(c_10, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, B_6))=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.45/1.85  tff(c_192, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_179, c_10])).
% 4.45/1.85  tff(c_237, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_192, c_216])).
% 4.45/1.85  tff(c_248, plain, (k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_149, c_237])).
% 4.45/1.85  tff(c_965, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_248])).
% 4.45/1.85  tff(c_969, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_965])).
% 4.45/1.85  tff(c_973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_969])).
% 4.45/1.85  tff(c_975, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_248])).
% 4.45/1.85  tff(c_974, plain, (k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_248])).
% 4.45/1.85  tff(c_16, plain, (![B_14, A_12]: (v5_tops_1(B_14, A_12) | k2_pre_topc(A_12, k1_tops_1(A_12, B_14))!=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.45/1.85  tff(c_1008, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_974, c_16])).
% 4.45/1.85  tff(c_1019, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_975, c_1008])).
% 4.45/1.85  tff(c_1023, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1019])).
% 4.45/1.85  tff(c_1175, plain, (![A_67, B_68]: (k3_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, k1_tops_1(A_67, B_68)))=k1_tops_1(A_67, k2_pre_topc(A_67, k3_subset_1(u1_struct_0(A_67), B_68))) | ~m1_subset_1(k2_pre_topc(A_67, k3_subset_1(u1_struct_0(A_67), B_68)), k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(superposition, [status(thm), theory('equality')], [c_216, c_14])).
% 4.45/1.85  tff(c_1205, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')))))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_192, c_1175])).
% 4.45/1.85  tff(c_1230, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_975, c_32, c_30, c_149, c_974, c_149, c_192, c_1205])).
% 4.45/1.85  tff(c_62, plain, (![A_33, B_34]: (m1_subset_1(k2_pre_topc(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.45/1.85  tff(c_65, plain, (![A_33, B_34]: (k3_subset_1(u1_struct_0(A_33), k3_subset_1(u1_struct_0(A_33), k2_pre_topc(A_33, B_34)))=k2_pre_topc(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_62, c_10])).
% 4.45/1.85  tff(c_1249, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1230, c_65])).
% 4.45/1.85  tff(c_1276, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_270, c_1249])).
% 4.45/1.85  tff(c_1278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1023, c_1276])).
% 4.45/1.85  tff(c_1280, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_1019])).
% 4.45/1.85  tff(c_1279, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_1019])).
% 4.45/1.85  tff(c_1281, plain, (v5_tops_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_1279])).
% 4.45/1.85  tff(c_1287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_820, c_1281])).
% 4.45/1.85  tff(c_1288, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_808])).
% 4.45/1.85  tff(c_1304, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1288, c_12])).
% 4.45/1.85  tff(c_1317, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1304])).
% 4.45/1.85  tff(c_1463, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1317])).
% 4.45/1.85  tff(c_1467, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1463])).
% 4.45/1.85  tff(c_1470, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1467])).
% 4.45/1.85  tff(c_1473, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1470])).
% 4.45/1.85  tff(c_1477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_270, c_1473])).
% 4.45/1.85  tff(c_1478, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1317])).
% 4.45/1.85  tff(c_1502, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_1478, c_10])).
% 4.45/1.85  tff(c_1605, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1502])).
% 4.45/1.85  tff(c_1626, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1605])).
% 4.45/1.85  tff(c_22, plain, (![A_17, B_19]: (k2_tops_1(A_17, k3_subset_1(u1_struct_0(A_17), B_19))=k2_tops_1(A_17, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.45/1.85  tff(c_183, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_179, c_22])).
% 4.45/1.85  tff(c_191, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_183])).
% 4.45/1.85  tff(c_1627, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1626, c_191])).
% 4.45/1.85  tff(c_108, plain, (![A_39, B_40]: (k2_tops_1(A_39, k3_subset_1(u1_struct_0(A_39), B_40))=k2_tops_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.45/1.85  tff(c_117, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_108])).
% 4.45/1.85  tff(c_123, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_117])).
% 4.45/1.85  tff(c_127, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_123, c_24])).
% 4.45/1.85  tff(c_131, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_127])).
% 4.45/1.85  tff(c_394, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_131])).
% 4.45/1.85  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.45/1.85  tff(c_397, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))), inference(resolution, [status(thm)], [c_394, c_2])).
% 4.45/1.85  tff(c_634, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))), inference(splitLeft, [status(thm)], [c_397])).
% 4.45/1.85  tff(c_1740, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1627, c_634])).
% 4.45/1.85  tff(c_1744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_1740])).
% 4.45/1.85  tff(c_1745, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_397])).
% 4.45/1.85  tff(c_1755, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1745, c_24])).
% 4.45/1.85  tff(c_1761, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1755])).
% 4.45/1.85  tff(c_2258, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1761])).
% 4.45/1.85  tff(c_2261, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_2258])).
% 4.45/1.85  tff(c_2265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_270, c_2261])).
% 4.45/1.85  tff(c_2267, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1761])).
% 4.45/1.85  tff(c_2275, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2267, c_22])).
% 4.45/1.85  tff(c_2289, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1745, c_2275])).
% 4.45/1.85  tff(c_2411, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_2289])).
% 4.45/1.85  tff(c_2423, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2411])).
% 4.45/1.85  tff(c_2425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_2423])).
% 4.45/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.85  
% 4.45/1.85  Inference rules
% 4.45/1.85  ----------------------
% 4.45/1.85  #Ref     : 0
% 4.45/1.85  #Sup     : 529
% 4.45/1.85  #Fact    : 0
% 4.45/1.85  #Define  : 0
% 4.45/1.85  #Split   : 33
% 4.45/1.85  #Chain   : 0
% 4.45/1.85  #Close   : 0
% 4.45/1.85  
% 4.45/1.85  Ordering : KBO
% 4.45/1.85  
% 4.45/1.85  Simplification rules
% 4.45/1.85  ----------------------
% 4.45/1.85  #Subsume      : 69
% 4.45/1.85  #Demod        : 836
% 4.45/1.85  #Tautology    : 228
% 4.45/1.85  #SimpNegUnit  : 10
% 4.45/1.85  #BackRed      : 13
% 4.45/1.85  
% 4.45/1.85  #Partial instantiations: 0
% 4.45/1.85  #Strategies tried      : 1
% 4.45/1.85  
% 4.45/1.85  Timing (in seconds)
% 4.45/1.85  ----------------------
% 4.65/1.86  Preprocessing        : 0.31
% 4.65/1.86  Parsing              : 0.18
% 4.65/1.86  CNF conversion       : 0.02
% 4.65/1.86  Main loop            : 0.71
% 4.65/1.86  Inferencing          : 0.24
% 4.65/1.86  Reduction            : 0.27
% 4.65/1.86  Demodulation         : 0.20
% 4.65/1.86  BG Simplification    : 0.03
% 4.65/1.86  Subsumption          : 0.14
% 4.65/1.86  Abstraction          : 0.05
% 4.65/1.86  MUC search           : 0.00
% 4.65/1.86  Cooper               : 0.00
% 4.65/1.86  Total                : 1.06
% 4.65/1.86  Index Insertion      : 0.00
% 4.65/1.86  Index Deletion       : 0.00
% 4.65/1.86  Index Matching       : 0.00
% 4.65/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
