%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:34 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 267 expanded)
%              Number of leaves         :   39 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  129 ( 425 expanded)
%              Number of equality atoms :   38 ( 166 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_43,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_101,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_131,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42,plain,(
    k1_tops_1('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12,plain,(
    ! [A_8] : k1_subset_1(A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_12] : k3_subset_1(A_12,k1_subset_1(A_12)) = k2_subset_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47,plain,(
    ! [A_12] : k3_subset_1(A_12,k1_subset_1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_48,plain,(
    ! [A_12] : k3_subset_1(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_47])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_365,plain,(
    ! [B_90,A_91] :
      ( v4_pre_topc(B_90,A_91)
      | ~ v1_xboole_0(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_384,plain,(
    ! [A_91] :
      ( v4_pre_topc(k1_xboole_0,A_91)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_20,c_365])).

tff(c_393,plain,(
    ! [A_92] :
      ( v4_pre_topc(k1_xboole_0,A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_384])).

tff(c_30,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_23] :
      ( v1_xboole_0(k1_struct_0(A_23))
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    ! [B_37,A_38] :
      ( ~ v1_xboole_0(B_37)
      | B_37 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_94,plain,(
    ! [A_40] :
      ( k1_struct_0(A_40) = k1_xboole_0
      | ~ l1_struct_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_32,c_84])).

tff(c_99,plain,(
    ! [A_41] :
      ( k1_struct_0(A_41) = k1_xboole_0
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_103,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_99])).

tff(c_151,plain,(
    ! [A_60] :
      ( k3_subset_1(u1_struct_0(A_60),k1_struct_0(A_60)) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_160,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k1_xboole_0) = k2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_151])).

tff(c_163,plain,
    ( u1_struct_0('#skF_2') = k2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_160])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_167,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_167])).

tff(c_172,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_225,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,B_75) = B_75
      | ~ v4_pre_topc(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_228,plain,(
    ! [B_75] :
      ( k2_pre_topc('#skF_2',B_75) = B_75
      | ~ v4_pre_topc(B_75,'#skF_2')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_225])).

tff(c_289,plain,(
    ! [B_80] :
      ( k2_pre_topc('#skF_2',B_80) = B_80
      | ~ v4_pre_topc(B_80,'#skF_2')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_228])).

tff(c_299,plain,
    ( k2_pre_topc('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_289])).

tff(c_300,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_396,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_393,c_300])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_396])).

tff(c_404,plain,(
    k2_pre_topc('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_217,plain,(
    ! [A_72,B_73] :
      ( k3_subset_1(A_72,k3_subset_1(A_72,B_73)) = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_221,plain,(
    ! [A_13] : k3_subset_1(A_13,k3_subset_1(A_13,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_224,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_221])).

tff(c_760,plain,(
    ! [A_132,B_133] :
      ( k3_subset_1(u1_struct_0(A_132),k2_pre_topc(A_132,k3_subset_1(u1_struct_0(A_132),B_133))) = k1_tops_1(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_789,plain,(
    ! [B_133] :
      ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_133))) = k1_tops_1('#skF_2',B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_760])).

tff(c_838,plain,(
    ! [B_135] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_135))) = k1_tops_1('#skF_2',B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_172,c_172,c_789])).

tff(c_864,plain,
    ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k1_xboole_0)) = k1_tops_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_838])).

tff(c_871,plain,
    ( k1_tops_1('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_404,c_864])).

tff(c_872,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_871])).

tff(c_877,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_872])).

tff(c_881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_877])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:36:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.47  
% 3.01/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.47  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1
% 3.01/1.47  
% 3.01/1.47  %Foreground sorts:
% 3.01/1.47  
% 3.01/1.47  
% 3.01/1.47  %Background operators:
% 3.01/1.47  
% 3.01/1.47  
% 3.01/1.47  %Foreground operators:
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.01/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.01/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.01/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.01/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.47  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.01/1.47  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.01/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.01/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.01/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.01/1.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.01/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.01/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.01/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.47  
% 3.01/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.01/1.49  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.01/1.49  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.01/1.49  tff(f_43, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.01/1.49  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.01/1.49  tff(f_51, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.01/1.49  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.01/1.49  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.01/1.49  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.01/1.49  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.01/1.49  tff(f_82, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 3.01/1.49  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.01/1.49  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 3.01/1.49  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.01/1.49  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.01/1.49  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.01/1.49  tff(c_131, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), A_51) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.01/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.01/1.49  tff(c_136, plain, (![A_51]: (r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_131, c_4])).
% 3.01/1.49  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.49  tff(c_42, plain, (k1_tops_1('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.49  tff(c_12, plain, (![A_8]: (k1_subset_1(A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.01/1.49  tff(c_14, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.01/1.49  tff(c_18, plain, (![A_12]: (k3_subset_1(A_12, k1_subset_1(A_12))=k2_subset_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.01/1.49  tff(c_47, plain, (![A_12]: (k3_subset_1(A_12, k1_subset_1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 3.01/1.49  tff(c_48, plain, (![A_12]: (k3_subset_1(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_47])).
% 3.01/1.49  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.49  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.49  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.49  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.01/1.49  tff(c_365, plain, (![B_90, A_91]: (v4_pre_topc(B_90, A_91) | ~v1_xboole_0(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.49  tff(c_384, plain, (![A_91]: (v4_pre_topc(k1_xboole_0, A_91) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(resolution, [status(thm)], [c_20, c_365])).
% 3.01/1.49  tff(c_393, plain, (![A_92]: (v4_pre_topc(k1_xboole_0, A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_384])).
% 3.01/1.49  tff(c_30, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.49  tff(c_32, plain, (![A_23]: (v1_xboole_0(k1_struct_0(A_23)) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.01/1.49  tff(c_77, plain, (![B_37, A_38]: (~v1_xboole_0(B_37) | B_37=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.01/1.49  tff(c_84, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_8, c_77])).
% 3.01/1.49  tff(c_94, plain, (![A_40]: (k1_struct_0(A_40)=k1_xboole_0 | ~l1_struct_0(A_40))), inference(resolution, [status(thm)], [c_32, c_84])).
% 3.01/1.49  tff(c_99, plain, (![A_41]: (k1_struct_0(A_41)=k1_xboole_0 | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_30, c_94])).
% 3.01/1.49  tff(c_103, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_99])).
% 3.01/1.49  tff(c_151, plain, (![A_60]: (k3_subset_1(u1_struct_0(A_60), k1_struct_0(A_60))=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.01/1.49  tff(c_160, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_xboole_0)=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103, c_151])).
% 3.01/1.49  tff(c_163, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_160])).
% 3.01/1.49  tff(c_164, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_163])).
% 3.01/1.49  tff(c_167, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_164])).
% 3.01/1.49  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_167])).
% 3.01/1.49  tff(c_172, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_163])).
% 3.01/1.49  tff(c_225, plain, (![A_74, B_75]: (k2_pre_topc(A_74, B_75)=B_75 | ~v4_pre_topc(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.01/1.49  tff(c_228, plain, (![B_75]: (k2_pre_topc('#skF_2', B_75)=B_75 | ~v4_pre_topc(B_75, '#skF_2') | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_225])).
% 3.01/1.49  tff(c_289, plain, (![B_80]: (k2_pre_topc('#skF_2', B_80)=B_80 | ~v4_pre_topc(B_80, '#skF_2') | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_228])).
% 3.01/1.49  tff(c_299, plain, (k2_pre_topc('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_20, c_289])).
% 3.01/1.49  tff(c_300, plain, (~v4_pre_topc(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_299])).
% 3.01/1.49  tff(c_396, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_393, c_300])).
% 3.01/1.49  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_396])).
% 3.01/1.49  tff(c_404, plain, (k2_pre_topc('#skF_2', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_299])).
% 3.01/1.49  tff(c_217, plain, (![A_72, B_73]: (k3_subset_1(A_72, k3_subset_1(A_72, B_73))=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.49  tff(c_221, plain, (![A_13]: (k3_subset_1(A_13, k3_subset_1(A_13, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_217])).
% 3.01/1.49  tff(c_224, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_221])).
% 3.01/1.49  tff(c_760, plain, (![A_132, B_133]: (k3_subset_1(u1_struct_0(A_132), k2_pre_topc(A_132, k3_subset_1(u1_struct_0(A_132), B_133)))=k1_tops_1(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.01/1.49  tff(c_789, plain, (![B_133]: (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_133)))=k1_tops_1('#skF_2', B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_760])).
% 3.01/1.49  tff(c_838, plain, (![B_135]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_135)))=k1_tops_1('#skF_2', B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_172, c_172, c_789])).
% 3.01/1.49  tff(c_864, plain, (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k1_xboole_0))=k1_tops_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_224, c_838])).
% 3.01/1.49  tff(c_871, plain, (k1_tops_1('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_404, c_864])).
% 3.01/1.49  tff(c_872, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_871])).
% 3.01/1.49  tff(c_877, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_872])).
% 3.01/1.49  tff(c_881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_877])).
% 3.01/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.49  
% 3.01/1.49  Inference rules
% 3.01/1.49  ----------------------
% 3.01/1.49  #Ref     : 0
% 3.01/1.49  #Sup     : 174
% 3.01/1.49  #Fact    : 0
% 3.01/1.49  #Define  : 0
% 3.01/1.49  #Split   : 3
% 3.01/1.49  #Chain   : 0
% 3.01/1.49  #Close   : 0
% 3.01/1.49  
% 3.01/1.49  Ordering : KBO
% 3.01/1.49  
% 3.01/1.49  Simplification rules
% 3.01/1.49  ----------------------
% 3.01/1.49  #Subsume      : 14
% 3.01/1.49  #Demod        : 74
% 3.01/1.49  #Tautology    : 49
% 3.01/1.49  #SimpNegUnit  : 5
% 3.01/1.49  #BackRed      : 0
% 3.01/1.49  
% 3.01/1.49  #Partial instantiations: 0
% 3.01/1.49  #Strategies tried      : 1
% 3.01/1.49  
% 3.01/1.49  Timing (in seconds)
% 3.01/1.49  ----------------------
% 3.01/1.49  Preprocessing        : 0.31
% 3.01/1.49  Parsing              : 0.18
% 3.01/1.49  CNF conversion       : 0.02
% 3.01/1.49  Main loop            : 0.37
% 3.01/1.49  Inferencing          : 0.15
% 3.01/1.49  Reduction            : 0.10
% 3.01/1.49  Demodulation         : 0.07
% 3.01/1.49  BG Simplification    : 0.02
% 3.01/1.50  Subsumption          : 0.07
% 3.01/1.50  Abstraction          : 0.02
% 3.01/1.50  MUC search           : 0.00
% 3.01/1.50  Cooper               : 0.00
% 3.01/1.50  Total                : 0.72
% 3.01/1.50  Index Insertion      : 0.00
% 3.01/1.50  Index Deletion       : 0.00
% 3.01/1.50  Index Matching       : 0.00
% 3.01/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
