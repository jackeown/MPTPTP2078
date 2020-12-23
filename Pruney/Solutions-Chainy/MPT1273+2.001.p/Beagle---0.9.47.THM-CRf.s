%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:01 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 172 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 362 expanded)
%              Number of equality atoms :   30 (  58 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_28,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_152,plain,(
    ! [B_42,A_43] :
      ( v2_tops_1(B_42,A_43)
      | k1_tops_1(A_43,B_42) != k1_xboole_0
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_162,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_152])).

tff(c_173,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_162])).

tff(c_174,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_173])).

tff(c_12,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_37,plain,(
    ! [A_27] :
      ( k1_struct_0(A_27) = k1_xboole_0
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    ! [A_28] :
      ( k1_struct_0(A_28) = k1_xboole_0
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_12,c_37])).

tff(c_46,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_51,plain,(
    ! [A_29] :
      ( k3_subset_1(u1_struct_0(A_29),k1_struct_0(A_29)) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_60,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_51])).

tff(c_63,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_70,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_66])).

tff(c_71,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_32,B_33] :
      ( k3_subset_1(A_32,k3_subset_1(A_32,B_33)) = B_33
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [A_34] : k3_subset_1(A_34,k3_subset_1(A_34,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_111,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_101])).

tff(c_30,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [A_21,B_23] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_21),B_23),A_21)
      | ~ v3_tops_1(B_23,A_21)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_292,plain,(
    ! [A_53,B_54] :
      ( k2_pre_topc(A_53,B_54) = k2_struct_0(A_53)
      | ~ v1_tops_1(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_302,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_292])).

tff(c_313,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_302])).

tff(c_315,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_99,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_91])).

tff(c_366,plain,(
    ! [A_59,B_60] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_59),B_60),A_59)
      | ~ v3_tops_1(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_373,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_366])).

tff(c_388,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_373])).

tff(c_389,plain,
    ( ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_388])).

tff(c_396,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_399,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_396])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_399])).

tff(c_405,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( k2_pre_topc(A_15,B_17) = k2_struct_0(A_15)
      | ~ v1_tops_1(B_17,A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_411,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_405,c_20])).

tff(c_427,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_411])).

tff(c_571,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_581,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_571])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_581])).

tff(c_586,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_16,plain,(
    ! [A_12,B_14] :
      ( k3_subset_1(u1_struct_0(A_12),k2_pre_topc(A_12,k3_subset_1(u1_struct_0(A_12),B_14))) = k1_tops_1(A_12,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_591,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_16])).

tff(c_595,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_111,c_591])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.38  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_1
% 2.58/1.38  
% 2.58/1.38  %Foreground sorts:
% 2.58/1.38  
% 2.58/1.38  
% 2.58/1.38  %Background operators:
% 2.58/1.38  
% 2.58/1.38  
% 2.58/1.38  %Foreground operators:
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.38  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.58/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.58/1.38  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.58/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.58/1.38  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.58/1.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.58/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.38  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.58/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.58/1.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.58/1.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.58/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.38  
% 2.83/1.39  tff(f_97, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 2.83/1.39  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 2.83/1.39  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.83/1.39  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.83/1.39  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.83/1.39  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.83/1.39  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.83/1.39  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 2.83/1.39  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.83/1.39  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.83/1.39  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.83/1.39  tff(c_28, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.39  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.39  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.39  tff(c_152, plain, (![B_42, A_43]: (v2_tops_1(B_42, A_43) | k1_tops_1(A_43, B_42)!=k1_xboole_0 | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.39  tff(c_162, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_152])).
% 2.83/1.39  tff(c_173, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_162])).
% 2.83/1.39  tff(c_174, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_173])).
% 2.83/1.39  tff(c_12, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.39  tff(c_37, plain, (![A_27]: (k1_struct_0(A_27)=k1_xboole_0 | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.39  tff(c_42, plain, (![A_28]: (k1_struct_0(A_28)=k1_xboole_0 | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_12, c_37])).
% 2.83/1.39  tff(c_46, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_42])).
% 2.83/1.39  tff(c_51, plain, (![A_29]: (k3_subset_1(u1_struct_0(A_29), k1_struct_0(A_29))=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.39  tff(c_60, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46, c_51])).
% 2.83/1.39  tff(c_63, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_60])).
% 2.83/1.39  tff(c_66, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_63])).
% 2.83/1.39  tff(c_70, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_66])).
% 2.83/1.39  tff(c_71, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_60])).
% 2.83/1.39  tff(c_6, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.39  tff(c_91, plain, (![A_32, B_33]: (k3_subset_1(A_32, k3_subset_1(A_32, B_33))=B_33 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.39  tff(c_101, plain, (![A_34]: (k3_subset_1(A_34, k3_subset_1(A_34, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_91])).
% 2.83/1.39  tff(c_111, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_71, c_101])).
% 2.83/1.39  tff(c_30, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.39  tff(c_26, plain, (![A_21, B_23]: (v1_tops_1(k3_subset_1(u1_struct_0(A_21), B_23), A_21) | ~v3_tops_1(B_23, A_21) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.83/1.39  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.39  tff(c_292, plain, (![A_53, B_54]: (k2_pre_topc(A_53, B_54)=k2_struct_0(A_53) | ~v1_tops_1(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.39  tff(c_302, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_292])).
% 2.83/1.39  tff(c_313, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_302])).
% 2.83/1.39  tff(c_315, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_313])).
% 2.83/1.39  tff(c_99, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_91])).
% 2.83/1.39  tff(c_366, plain, (![A_59, B_60]: (v1_tops_1(k3_subset_1(u1_struct_0(A_59), B_60), A_59) | ~v3_tops_1(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.83/1.39  tff(c_373, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_366])).
% 2.83/1.39  tff(c_388, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_373])).
% 2.83/1.39  tff(c_389, plain, (~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_315, c_388])).
% 2.83/1.39  tff(c_396, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_389])).
% 2.83/1.39  tff(c_399, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_396])).
% 2.83/1.39  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_399])).
% 2.83/1.39  tff(c_405, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_389])).
% 2.83/1.39  tff(c_20, plain, (![A_15, B_17]: (k2_pre_topc(A_15, B_17)=k2_struct_0(A_15) | ~v1_tops_1(B_17, A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.39  tff(c_411, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_405, c_20])).
% 2.83/1.39  tff(c_427, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_411])).
% 2.83/1.39  tff(c_571, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_427])).
% 2.83/1.39  tff(c_581, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_571])).
% 2.83/1.39  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_581])).
% 2.83/1.39  tff(c_586, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_427])).
% 2.83/1.39  tff(c_16, plain, (![A_12, B_14]: (k3_subset_1(u1_struct_0(A_12), k2_pre_topc(A_12, k3_subset_1(u1_struct_0(A_12), B_14)))=k1_tops_1(A_12, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.83/1.39  tff(c_591, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_586, c_16])).
% 2.83/1.39  tff(c_595, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_111, c_591])).
% 2.83/1.39  tff(c_597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_595])).
% 2.83/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.39  
% 2.83/1.39  Inference rules
% 2.83/1.39  ----------------------
% 2.83/1.39  #Ref     : 0
% 2.83/1.39  #Sup     : 128
% 2.83/1.39  #Fact    : 0
% 2.83/1.39  #Define  : 0
% 2.83/1.39  #Split   : 9
% 2.83/1.39  #Chain   : 0
% 2.83/1.39  #Close   : 0
% 2.83/1.39  
% 2.83/1.39  Ordering : KBO
% 2.83/1.39  
% 2.83/1.39  Simplification rules
% 2.83/1.39  ----------------------
% 2.83/1.39  #Subsume      : 8
% 2.83/1.39  #Demod        : 67
% 2.83/1.39  #Tautology    : 41
% 2.83/1.39  #SimpNegUnit  : 10
% 2.83/1.39  #BackRed      : 0
% 2.83/1.39  
% 2.83/1.39  #Partial instantiations: 0
% 2.83/1.39  #Strategies tried      : 1
% 2.83/1.39  
% 2.83/1.39  Timing (in seconds)
% 2.83/1.39  ----------------------
% 2.83/1.39  Preprocessing        : 0.31
% 2.83/1.39  Parsing              : 0.17
% 2.83/1.39  CNF conversion       : 0.02
% 2.83/1.39  Main loop            : 0.31
% 2.83/1.39  Inferencing          : 0.12
% 2.83/1.39  Reduction            : 0.10
% 2.83/1.40  Demodulation         : 0.07
% 2.83/1.40  BG Simplification    : 0.02
% 2.83/1.40  Subsumption          : 0.05
% 2.83/1.40  Abstraction          : 0.02
% 2.83/1.40  MUC search           : 0.00
% 2.83/1.40  Cooper               : 0.00
% 2.83/1.40  Total                : 0.65
% 2.83/1.40  Index Insertion      : 0.00
% 2.83/1.40  Index Deletion       : 0.00
% 2.83/1.40  Index Matching       : 0.00
% 2.83/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
