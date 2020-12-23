%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:24 EST 2020

% Result     : Theorem 14.60s
% Output     : CNFRefutation 14.60s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 330 expanded)
%              Number of leaves         :   50 ( 130 expanded)
%              Depth                    :   15
%              Number of atoms          :  187 ( 611 expanded)
%              Number of equality atoms :   84 ( 206 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_120,axiom,(
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

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_30006,plain,(
    ! [A_669,B_670,C_671] :
      ( k7_subset_1(A_669,B_670,C_671) = k4_xboole_0(B_670,C_671)
      | ~ m1_subset_1(B_670,k1_zfmisc_1(A_669)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30022,plain,(
    ! [C_671] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_671) = k4_xboole_0('#skF_2',C_671) ),
    inference(resolution,[status(thm)],[c_66,c_30006])).

tff(c_78,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_148,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_237,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4708,plain,(
    ! [B_234,A_235] :
      ( v4_pre_topc(B_234,A_235)
      | k2_pre_topc(A_235,B_234) != B_234
      | ~ v2_pre_topc(A_235)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ l1_pre_topc(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4750,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_4708])).

tff(c_4782,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_4750])).

tff(c_4783,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_4782])).

tff(c_5584,plain,(
    ! [A_255,B_256] :
      ( k4_subset_1(u1_struct_0(A_255),B_256,k2_tops_1(A_255,B_256)) = k2_pre_topc(A_255,B_256)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5614,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_5584])).

tff(c_5644,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5614])).

tff(c_2325,plain,(
    ! [A_177,B_178,C_179] :
      ( k7_subset_1(A_177,B_178,C_179) = k4_xboole_0(B_178,C_179)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2351,plain,(
    ! [C_182] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_182) = k4_xboole_0('#skF_2',C_182) ),
    inference(resolution,[status(thm)],[c_66,c_2325])).

tff(c_2363,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2351])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_238,plain,(
    ! [A_86,B_87] :
      ( k2_xboole_0(A_86,B_87) = B_87
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_285,plain,(
    ! [A_89,B_90] : k2_xboole_0(k4_xboole_0(A_89,B_90),A_89) = A_89 ),
    inference(resolution,[status(thm)],[c_14,c_238])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_291,plain,(
    ! [A_89,B_90] : k2_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = A_89 ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_2])).

tff(c_3164,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2363,c_291])).

tff(c_2913,plain,(
    ! [A_199,B_200,C_201] :
      ( m1_subset_1(k7_subset_1(A_199,B_200,C_201),k1_zfmisc_1(A_199))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2939,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2913])).

tff(c_2953,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2939])).

tff(c_48,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3618,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2953,c_48])).

tff(c_50,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,k1_zfmisc_1(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3840,plain,(
    ! [A_220,B_221,C_222] :
      ( k4_subset_1(A_220,B_221,C_222) = k2_xboole_0(B_221,C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(A_220))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26096,plain,(
    ! [B_523,B_524,A_525] :
      ( k4_subset_1(B_523,B_524,A_525) = k2_xboole_0(B_524,A_525)
      | ~ m1_subset_1(B_524,k1_zfmisc_1(B_523))
      | ~ r1_tarski(A_525,B_523) ) ),
    inference(resolution,[status(thm)],[c_50,c_3840])).

tff(c_26936,plain,(
    ! [A_532] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_532) = k2_xboole_0('#skF_2',A_532)
      | ~ r1_tarski(A_532,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_66,c_26096])).

tff(c_27004,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3618,c_26936])).

tff(c_27060,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5644,c_3164,c_27004])).

tff(c_27062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4783,c_27060])).

tff(c_27063,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_27286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_27063])).

tff(c_27287,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_27400,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27287,c_72])).

tff(c_30040,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30022,c_27400])).

tff(c_30937,plain,(
    ! [A_705,B_706] :
      ( r1_tarski(k2_tops_1(A_705,B_706),B_706)
      | ~ v4_pre_topc(B_706,A_705)
      | ~ m1_subset_1(B_706,k1_zfmisc_1(u1_struct_0(A_705)))
      | ~ l1_pre_topc(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_30961,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_30937])).

tff(c_30982,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_27287,c_30961])).

tff(c_32302,plain,(
    ! [A_738,B_739] :
      ( k7_subset_1(u1_struct_0(A_738),B_739,k2_tops_1(A_738,B_739)) = k1_tops_1(A_738,B_739)
      | ~ m1_subset_1(B_739,k1_zfmisc_1(u1_struct_0(A_738)))
      | ~ l1_pre_topc(A_738) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_32330,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_32302])).

tff(c_32357,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30022,c_32330])).

tff(c_29508,plain,(
    ! [A_654,B_655] :
      ( k4_xboole_0(A_654,B_655) = k3_subset_1(A_654,B_655)
      | ~ m1_subset_1(B_655,k1_zfmisc_1(A_654)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37623,plain,(
    ! [B_820,A_821] :
      ( k4_xboole_0(B_820,A_821) = k3_subset_1(B_820,A_821)
      | ~ r1_tarski(A_821,B_820) ) ),
    inference(resolution,[status(thm)],[c_50,c_29508])).

tff(c_37731,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30982,c_37623])).

tff(c_37819,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32357,c_37731])).

tff(c_28045,plain,(
    ! [A_602,B_603] :
      ( k3_subset_1(A_602,k3_subset_1(A_602,B_603)) = B_603
      | ~ m1_subset_1(B_603,k1_zfmisc_1(A_602)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28054,plain,(
    ! [B_51,A_50] :
      ( k3_subset_1(B_51,k3_subset_1(B_51,A_50)) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_50,c_28045])).

tff(c_38117,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_37819,c_28054])).

tff(c_38127,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30982,c_38117])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30996,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30982,c_8])).

tff(c_101,plain,(
    ! [B_77,A_78] : k2_xboole_0(B_77,A_78) = k2_xboole_0(A_78,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [A_78] : k2_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_10])).

tff(c_27559,plain,(
    ! [A_571,B_572] : k2_xboole_0(A_571,k4_xboole_0(B_572,A_571)) = k2_xboole_0(A_571,B_572) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27570,plain,(
    ! [B_572] : k4_xboole_0(B_572,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_572) ),
    inference(superposition,[status(thm),theory(equality)],[c_27559,c_117])).

tff(c_27590,plain,(
    ! [B_572] : k4_xboole_0(B_572,k1_xboole_0) = B_572 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_27570])).

tff(c_27363,plain,(
    ! [A_555,B_556] :
      ( k2_xboole_0(A_555,B_556) = B_556
      | ~ r1_tarski(A_555,B_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27368,plain,(
    ! [A_557,B_558] : k2_xboole_0(k4_xboole_0(A_557,B_558),A_557) = A_557 ),
    inference(resolution,[status(thm)],[c_14,c_27363])).

tff(c_27381,plain,(
    ! [B_558] : k4_xboole_0(k1_xboole_0,B_558) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27368,c_10])).

tff(c_27632,plain,(
    ! [A_574,B_575] : k4_xboole_0(A_574,k4_xboole_0(A_574,B_575)) = k3_xboole_0(A_574,B_575) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_27681,plain,(
    ! [B_576] : k3_xboole_0(k1_xboole_0,B_576) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27632,c_27381])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27689,plain,(
    ! [B_576] : k3_xboole_0(B_576,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27681,c_4])).

tff(c_27663,plain,(
    ! [B_572] : k4_xboole_0(B_572,B_572) = k3_xboole_0(B_572,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_27590,c_27632])).

tff(c_28091,plain,(
    ! [B_572] : k4_xboole_0(B_572,B_572) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27689,c_27663])).

tff(c_28748,plain,(
    ! [A_639,B_640,C_641] : k4_xboole_0(k4_xboole_0(A_639,B_640),C_641) = k4_xboole_0(A_639,k2_xboole_0(B_640,C_641)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28814,plain,(
    ! [B_572,C_641] : k4_xboole_0(B_572,k2_xboole_0(B_572,C_641)) = k4_xboole_0(k1_xboole_0,C_641) ),
    inference(superposition,[status(thm),theory(equality)],[c_28091,c_28748])).

tff(c_28970,plain,(
    ! [B_644,C_645] : k4_xboole_0(B_644,k2_xboole_0(B_644,C_645)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27381,c_28814])).

tff(c_22,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28994,plain,(
    ! [B_644,C_645] : k3_xboole_0(B_644,k2_xboole_0(B_644,C_645)) = k4_xboole_0(B_644,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28970,c_22])).

tff(c_29069,plain,(
    ! [B_644,C_645] : k3_xboole_0(B_644,k2_xboole_0(B_644,C_645)) = B_644 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27590,c_28994])).

tff(c_24,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_30099,plain,(
    ! [A_675,C_676] : k7_subset_1(A_675,A_675,C_676) = k4_xboole_0(A_675,C_676) ),
    inference(resolution,[status(thm)],[c_79,c_30006])).

tff(c_32,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k7_subset_1(A_30,B_31,C_32),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30109,plain,(
    ! [A_675,C_676] :
      ( m1_subset_1(k4_xboole_0(A_675,C_676),k1_zfmisc_1(A_675))
      | ~ m1_subset_1(A_675,k1_zfmisc_1(A_675)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30099,c_32])).

tff(c_30123,plain,(
    ! [A_677,C_678] : m1_subset_1(k4_xboole_0(A_677,C_678),k1_zfmisc_1(A_677)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_30109])).

tff(c_30197,plain,(
    ! [A_679,B_680] : m1_subset_1(k3_xboole_0(A_679,B_680),k1_zfmisc_1(A_679)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_30123])).

tff(c_30247,plain,(
    ! [B_681,A_682] : m1_subset_1(k3_xboole_0(B_681,A_682),k1_zfmisc_1(A_682)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_30197])).

tff(c_30265,plain,(
    ! [B_644,C_645] : m1_subset_1(B_644,k1_zfmisc_1(k2_xboole_0(B_644,C_645))) ),
    inference(superposition,[status(thm),theory(equality)],[c_29069,c_30247])).

tff(c_31000,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30996,c_30265])).

tff(c_30,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k3_subset_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_55628,plain,(
    ! [A_1021,B_1022] :
      ( k4_xboole_0(A_1021,k3_subset_1(A_1021,B_1022)) = k3_subset_1(A_1021,k3_subset_1(A_1021,B_1022))
      | ~ m1_subset_1(B_1022,k1_zfmisc_1(A_1021)) ) ),
    inference(resolution,[status(thm)],[c_30,c_29508])).

tff(c_55662,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_31000,c_55628])).

tff(c_55709,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38127,c_37819,c_37819,c_55662])).

tff(c_55711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30040,c_55709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.60/7.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.60/7.32  
% 14.60/7.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.60/7.32  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 14.60/7.32  
% 14.60/7.32  %Foreground sorts:
% 14.60/7.32  
% 14.60/7.32  
% 14.60/7.32  %Background operators:
% 14.60/7.32  
% 14.60/7.32  
% 14.60/7.32  %Foreground operators:
% 14.60/7.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.60/7.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.60/7.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.60/7.32  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.60/7.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.60/7.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.60/7.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.60/7.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.60/7.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.60/7.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.60/7.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.60/7.32  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.60/7.32  tff('#skF_2', type, '#skF_2': $i).
% 14.60/7.32  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.60/7.32  tff('#skF_1', type, '#skF_1': $i).
% 14.60/7.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.60/7.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.60/7.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.60/7.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.60/7.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.60/7.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.60/7.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.60/7.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.60/7.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.60/7.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.60/7.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.60/7.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.60/7.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.60/7.32  
% 14.60/7.34  tff(f_162, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 14.60/7.34  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.60/7.34  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 14.60/7.34  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 14.60/7.34  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.60/7.34  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.60/7.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.60/7.34  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 14.60/7.34  tff(f_99, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.60/7.34  tff(f_83, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.60/7.34  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 14.60/7.34  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 14.60/7.34  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 14.60/7.34  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.60/7.34  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 14.60/7.34  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.60/7.34  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.60/7.34  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.60/7.34  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.60/7.34  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 14.60/7.34  tff(f_61, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 14.60/7.34  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 14.60/7.34  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.60/7.34  tff(c_30006, plain, (![A_669, B_670, C_671]: (k7_subset_1(A_669, B_670, C_671)=k4_xboole_0(B_670, C_671) | ~m1_subset_1(B_670, k1_zfmisc_1(A_669)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.60/7.34  tff(c_30022, plain, (![C_671]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_671)=k4_xboole_0('#skF_2', C_671))), inference(resolution, [status(thm)], [c_66, c_30006])).
% 14.60/7.34  tff(c_78, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.60/7.34  tff(c_148, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_78])).
% 14.60/7.34  tff(c_72, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.60/7.34  tff(c_237, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 14.60/7.34  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.60/7.34  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.60/7.34  tff(c_4708, plain, (![B_234, A_235]: (v4_pre_topc(B_234, A_235) | k2_pre_topc(A_235, B_234)!=B_234 | ~v2_pre_topc(A_235) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_235))) | ~l1_pre_topc(A_235))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.60/7.34  tff(c_4750, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_4708])).
% 14.60/7.34  tff(c_4782, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_4750])).
% 14.60/7.34  tff(c_4783, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_237, c_4782])).
% 14.60/7.34  tff(c_5584, plain, (![A_255, B_256]: (k4_subset_1(u1_struct_0(A_255), B_256, k2_tops_1(A_255, B_256))=k2_pre_topc(A_255, B_256) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.60/7.34  tff(c_5614, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_5584])).
% 14.60/7.34  tff(c_5644, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5614])).
% 14.60/7.34  tff(c_2325, plain, (![A_177, B_178, C_179]: (k7_subset_1(A_177, B_178, C_179)=k4_xboole_0(B_178, C_179) | ~m1_subset_1(B_178, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.60/7.34  tff(c_2351, plain, (![C_182]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_182)=k4_xboole_0('#skF_2', C_182))), inference(resolution, [status(thm)], [c_66, c_2325])).
% 14.60/7.34  tff(c_2363, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_148, c_2351])).
% 14.60/7.34  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.60/7.34  tff(c_238, plain, (![A_86, B_87]: (k2_xboole_0(A_86, B_87)=B_87 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.60/7.34  tff(c_285, plain, (![A_89, B_90]: (k2_xboole_0(k4_xboole_0(A_89, B_90), A_89)=A_89)), inference(resolution, [status(thm)], [c_14, c_238])).
% 14.60/7.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.60/7.34  tff(c_291, plain, (![A_89, B_90]: (k2_xboole_0(A_89, k4_xboole_0(A_89, B_90))=A_89)), inference(superposition, [status(thm), theory('equality')], [c_285, c_2])).
% 14.60/7.34  tff(c_3164, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2363, c_291])).
% 14.60/7.34  tff(c_2913, plain, (![A_199, B_200, C_201]: (m1_subset_1(k7_subset_1(A_199, B_200, C_201), k1_zfmisc_1(A_199)) | ~m1_subset_1(B_200, k1_zfmisc_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.60/7.34  tff(c_2939, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_2913])).
% 14.60/7.34  tff(c_2953, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2939])).
% 14.60/7.34  tff(c_48, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.60/7.34  tff(c_3618, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2953, c_48])).
% 14.60/7.34  tff(c_50, plain, (![A_50, B_51]: (m1_subset_1(A_50, k1_zfmisc_1(B_51)) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.60/7.34  tff(c_3840, plain, (![A_220, B_221, C_222]: (k4_subset_1(A_220, B_221, C_222)=k2_xboole_0(B_221, C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(A_220)) | ~m1_subset_1(B_221, k1_zfmisc_1(A_220)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.60/7.34  tff(c_26096, plain, (![B_523, B_524, A_525]: (k4_subset_1(B_523, B_524, A_525)=k2_xboole_0(B_524, A_525) | ~m1_subset_1(B_524, k1_zfmisc_1(B_523)) | ~r1_tarski(A_525, B_523))), inference(resolution, [status(thm)], [c_50, c_3840])).
% 14.60/7.34  tff(c_26936, plain, (![A_532]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_532)=k2_xboole_0('#skF_2', A_532) | ~r1_tarski(A_532, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_66, c_26096])).
% 14.60/7.34  tff(c_27004, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3618, c_26936])).
% 14.60/7.34  tff(c_27060, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5644, c_3164, c_27004])).
% 14.60/7.34  tff(c_27062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4783, c_27060])).
% 14.60/7.34  tff(c_27063, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_72])).
% 14.60/7.34  tff(c_27286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_27063])).
% 14.60/7.34  tff(c_27287, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_78])).
% 14.60/7.34  tff(c_27400, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27287, c_72])).
% 14.60/7.34  tff(c_30040, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30022, c_27400])).
% 14.60/7.34  tff(c_30937, plain, (![A_705, B_706]: (r1_tarski(k2_tops_1(A_705, B_706), B_706) | ~v4_pre_topc(B_706, A_705) | ~m1_subset_1(B_706, k1_zfmisc_1(u1_struct_0(A_705))) | ~l1_pre_topc(A_705))), inference(cnfTransformation, [status(thm)], [f_143])).
% 14.60/7.34  tff(c_30961, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_30937])).
% 14.60/7.34  tff(c_30982, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_27287, c_30961])).
% 14.60/7.34  tff(c_32302, plain, (![A_738, B_739]: (k7_subset_1(u1_struct_0(A_738), B_739, k2_tops_1(A_738, B_739))=k1_tops_1(A_738, B_739) | ~m1_subset_1(B_739, k1_zfmisc_1(u1_struct_0(A_738))) | ~l1_pre_topc(A_738))), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.60/7.34  tff(c_32330, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_32302])).
% 14.60/7.34  tff(c_32357, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30022, c_32330])).
% 14.60/7.34  tff(c_29508, plain, (![A_654, B_655]: (k4_xboole_0(A_654, B_655)=k3_subset_1(A_654, B_655) | ~m1_subset_1(B_655, k1_zfmisc_1(A_654)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.60/7.34  tff(c_37623, plain, (![B_820, A_821]: (k4_xboole_0(B_820, A_821)=k3_subset_1(B_820, A_821) | ~r1_tarski(A_821, B_820))), inference(resolution, [status(thm)], [c_50, c_29508])).
% 14.60/7.34  tff(c_37731, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30982, c_37623])).
% 14.60/7.34  tff(c_37819, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32357, c_37731])).
% 14.60/7.34  tff(c_28045, plain, (![A_602, B_603]: (k3_subset_1(A_602, k3_subset_1(A_602, B_603))=B_603 | ~m1_subset_1(B_603, k1_zfmisc_1(A_602)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.60/7.34  tff(c_28054, plain, (![B_51, A_50]: (k3_subset_1(B_51, k3_subset_1(B_51, A_50))=A_50 | ~r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_50, c_28045])).
% 14.60/7.34  tff(c_38117, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_37819, c_28054])).
% 14.60/7.34  tff(c_38127, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30982, c_38117])).
% 14.60/7.34  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.60/7.34  tff(c_30996, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30982, c_8])).
% 14.60/7.34  tff(c_101, plain, (![B_77, A_78]: (k2_xboole_0(B_77, A_78)=k2_xboole_0(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.60/7.34  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.60/7.34  tff(c_117, plain, (![A_78]: (k2_xboole_0(k1_xboole_0, A_78)=A_78)), inference(superposition, [status(thm), theory('equality')], [c_101, c_10])).
% 14.60/7.34  tff(c_27559, plain, (![A_571, B_572]: (k2_xboole_0(A_571, k4_xboole_0(B_572, A_571))=k2_xboole_0(A_571, B_572))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.60/7.34  tff(c_27570, plain, (![B_572]: (k4_xboole_0(B_572, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_572))), inference(superposition, [status(thm), theory('equality')], [c_27559, c_117])).
% 14.60/7.34  tff(c_27590, plain, (![B_572]: (k4_xboole_0(B_572, k1_xboole_0)=B_572)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_27570])).
% 14.60/7.34  tff(c_27363, plain, (![A_555, B_556]: (k2_xboole_0(A_555, B_556)=B_556 | ~r1_tarski(A_555, B_556))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.60/7.34  tff(c_27368, plain, (![A_557, B_558]: (k2_xboole_0(k4_xboole_0(A_557, B_558), A_557)=A_557)), inference(resolution, [status(thm)], [c_14, c_27363])).
% 14.60/7.34  tff(c_27381, plain, (![B_558]: (k4_xboole_0(k1_xboole_0, B_558)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27368, c_10])).
% 14.60/7.34  tff(c_27632, plain, (![A_574, B_575]: (k4_xboole_0(A_574, k4_xboole_0(A_574, B_575))=k3_xboole_0(A_574, B_575))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.60/7.34  tff(c_27681, plain, (![B_576]: (k3_xboole_0(k1_xboole_0, B_576)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27632, c_27381])).
% 14.60/7.34  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.60/7.34  tff(c_27689, plain, (![B_576]: (k3_xboole_0(B_576, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27681, c_4])).
% 14.60/7.34  tff(c_27663, plain, (![B_572]: (k4_xboole_0(B_572, B_572)=k3_xboole_0(B_572, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_27590, c_27632])).
% 14.60/7.34  tff(c_28091, plain, (![B_572]: (k4_xboole_0(B_572, B_572)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27689, c_27663])).
% 14.60/7.34  tff(c_28748, plain, (![A_639, B_640, C_641]: (k4_xboole_0(k4_xboole_0(A_639, B_640), C_641)=k4_xboole_0(A_639, k2_xboole_0(B_640, C_641)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.60/7.34  tff(c_28814, plain, (![B_572, C_641]: (k4_xboole_0(B_572, k2_xboole_0(B_572, C_641))=k4_xboole_0(k1_xboole_0, C_641))), inference(superposition, [status(thm), theory('equality')], [c_28091, c_28748])).
% 14.60/7.34  tff(c_28970, plain, (![B_644, C_645]: (k4_xboole_0(B_644, k2_xboole_0(B_644, C_645))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27381, c_28814])).
% 14.60/7.34  tff(c_22, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.60/7.34  tff(c_28994, plain, (![B_644, C_645]: (k3_xboole_0(B_644, k2_xboole_0(B_644, C_645))=k4_xboole_0(B_644, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28970, c_22])).
% 14.60/7.34  tff(c_29069, plain, (![B_644, C_645]: (k3_xboole_0(B_644, k2_xboole_0(B_644, C_645))=B_644)), inference(demodulation, [status(thm), theory('equality')], [c_27590, c_28994])).
% 14.60/7.34  tff(c_24, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.60/7.34  tff(c_28, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.60/7.34  tff(c_79, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 14.60/7.34  tff(c_30099, plain, (![A_675, C_676]: (k7_subset_1(A_675, A_675, C_676)=k4_xboole_0(A_675, C_676))), inference(resolution, [status(thm)], [c_79, c_30006])).
% 14.60/7.34  tff(c_32, plain, (![A_30, B_31, C_32]: (m1_subset_1(k7_subset_1(A_30, B_31, C_32), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.60/7.34  tff(c_30109, plain, (![A_675, C_676]: (m1_subset_1(k4_xboole_0(A_675, C_676), k1_zfmisc_1(A_675)) | ~m1_subset_1(A_675, k1_zfmisc_1(A_675)))), inference(superposition, [status(thm), theory('equality')], [c_30099, c_32])).
% 14.60/7.34  tff(c_30123, plain, (![A_677, C_678]: (m1_subset_1(k4_xboole_0(A_677, C_678), k1_zfmisc_1(A_677)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_30109])).
% 14.60/7.34  tff(c_30197, plain, (![A_679, B_680]: (m1_subset_1(k3_xboole_0(A_679, B_680), k1_zfmisc_1(A_679)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_30123])).
% 14.60/7.34  tff(c_30247, plain, (![B_681, A_682]: (m1_subset_1(k3_xboole_0(B_681, A_682), k1_zfmisc_1(A_682)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_30197])).
% 14.60/7.34  tff(c_30265, plain, (![B_644, C_645]: (m1_subset_1(B_644, k1_zfmisc_1(k2_xboole_0(B_644, C_645))))), inference(superposition, [status(thm), theory('equality')], [c_29069, c_30247])).
% 14.60/7.34  tff(c_31000, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_30996, c_30265])).
% 14.60/7.34  tff(c_30, plain, (![A_28, B_29]: (m1_subset_1(k3_subset_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.60/7.34  tff(c_55628, plain, (![A_1021, B_1022]: (k4_xboole_0(A_1021, k3_subset_1(A_1021, B_1022))=k3_subset_1(A_1021, k3_subset_1(A_1021, B_1022)) | ~m1_subset_1(B_1022, k1_zfmisc_1(A_1021)))), inference(resolution, [status(thm)], [c_30, c_29508])).
% 14.60/7.34  tff(c_55662, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_31000, c_55628])).
% 14.60/7.34  tff(c_55709, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38127, c_37819, c_37819, c_55662])).
% 14.60/7.34  tff(c_55711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30040, c_55709])).
% 14.60/7.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.60/7.34  
% 14.60/7.34  Inference rules
% 14.60/7.34  ----------------------
% 14.60/7.34  #Ref     : 0
% 14.60/7.34  #Sup     : 13881
% 14.60/7.34  #Fact    : 0
% 14.60/7.34  #Define  : 0
% 14.60/7.34  #Split   : 2
% 14.60/7.34  #Chain   : 0
% 14.60/7.34  #Close   : 0
% 14.60/7.34  
% 14.60/7.34  Ordering : KBO
% 14.60/7.34  
% 14.60/7.34  Simplification rules
% 14.60/7.34  ----------------------
% 14.60/7.34  #Subsume      : 240
% 14.60/7.34  #Demod        : 10943
% 14.60/7.34  #Tautology    : 8811
% 14.60/7.34  #SimpNegUnit  : 4
% 14.60/7.34  #BackRed      : 8
% 14.60/7.34  
% 14.60/7.34  #Partial instantiations: 0
% 14.60/7.34  #Strategies tried      : 1
% 14.60/7.34  
% 14.60/7.34  Timing (in seconds)
% 14.60/7.34  ----------------------
% 14.60/7.34  Preprocessing        : 0.36
% 14.60/7.34  Parsing              : 0.19
% 14.60/7.34  CNF conversion       : 0.03
% 14.60/7.34  Main loop            : 6.17
% 14.60/7.34  Inferencing          : 1.05
% 14.60/7.34  Reduction            : 3.41
% 14.60/7.34  Demodulation         : 2.97
% 14.60/7.34  BG Simplification    : 0.12
% 14.60/7.34  Subsumption          : 1.24
% 14.60/7.34  Abstraction          : 0.20
% 14.60/7.34  MUC search           : 0.00
% 14.60/7.35  Cooper               : 0.00
% 14.60/7.35  Total                : 6.58
% 14.60/7.35  Index Insertion      : 0.00
% 14.60/7.35  Index Deletion       : 0.00
% 14.60/7.35  Index Matching       : 0.00
% 14.60/7.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
