%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:04 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 144 expanded)
%              Number of leaves         :   40 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :  144 ( 315 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_44,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_58,plain,
    ( k2_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_76,plain,(
    ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_400,plain,(
    ! [B_109,A_110] :
      ( v2_tops_1(B_109,A_110)
      | k1_tops_1(A_110,B_109) != k1_xboole_0
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_415,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_400])).

tff(c_425,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_415])).

tff(c_427,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_483,plain,(
    ! [A_120,B_121] :
      ( k1_tops_1(A_120,B_121) = k1_xboole_0
      | ~ v2_tops_1(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_494,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_483])).

tff(c_503,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_494])).

tff(c_504,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_503])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_77,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_64])).

tff(c_638,plain,(
    ! [B_134,A_135] :
      ( v2_tops_1(B_134,A_135)
      | ~ r1_tarski(B_134,k2_tops_1(A_135,B_134))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_649,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_638])).

tff(c_656,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_12,c_649])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_504,c_656])).

tff(c_659,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_52,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_997,plain,(
    ! [B_165,A_166] :
      ( v3_tops_1(B_165,A_166)
      | ~ v4_pre_topc(B_165,A_166)
      | ~ v2_tops_1(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1008,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_997])).

tff(c_1017,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_659,c_52,c_1008])).

tff(c_1019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1017])).

tff(c_1020,plain,(
    k2_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1098,plain,(
    ! [A_180,B_181] : k2_xboole_0(k3_xboole_0(A_180,B_181),k4_xboole_0(A_180,B_181)) = A_180 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1110,plain,(
    ! [A_182] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_182,k1_xboole_0)) = A_182 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1098])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1022,plain,(
    ! [A_167,B_168] :
      ( r1_tarski(A_167,B_168)
      | ~ m1_subset_1(A_167,k1_zfmisc_1(B_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1030,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_22,c_1022])).

tff(c_1034,plain,(
    ! [A_170,B_171] :
      ( k2_xboole_0(A_170,B_171) = B_171
      | ~ r1_tarski(A_170,B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1045,plain,(
    ! [A_16] : k2_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(resolution,[status(thm)],[c_1030,c_1034])).

tff(c_1116,plain,(
    ! [A_182] : k4_xboole_0(A_182,k1_xboole_0) = A_182 ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_1045])).

tff(c_1207,plain,(
    ! [A_203,B_204,C_205] :
      ( k7_subset_1(A_203,B_204,C_205) = k4_xboole_0(B_204,C_205)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1215,plain,(
    ! [C_205] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_205) = k4_xboole_0('#skF_3',C_205) ),
    inference(resolution,[status(thm)],[c_54,c_1207])).

tff(c_1392,plain,(
    ! [A_234,B_235] :
      ( k2_pre_topc(A_234,B_235) = B_235
      | ~ v4_pre_topc(B_235,A_234)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1403,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1392])).

tff(c_1412,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1403])).

tff(c_1021,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1217,plain,(
    ! [B_206,A_207] :
      ( v2_tops_1(B_206,A_207)
      | ~ v3_tops_1(B_206,A_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1224,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ v3_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1217])).

tff(c_1232,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1021,c_1224])).

tff(c_1437,plain,(
    ! [A_240,B_241] :
      ( k1_tops_1(A_240,B_241) = k1_xboole_0
      | ~ v2_tops_1(B_241,A_240)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1448,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1437])).

tff(c_1457,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1232,c_1448])).

tff(c_1748,plain,(
    ! [A_260,B_261] :
      ( k7_subset_1(u1_struct_0(A_260),k2_pre_topc(A_260,B_261),k1_tops_1(A_260,B_261)) = k2_tops_1(A_260,B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1760,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),k1_xboole_0) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1457,c_1748])).

tff(c_1769,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1116,c_1215,c_1412,c_1760])).

tff(c_1771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1020,c_1769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.27  % Computer   : n003.cluster.edu
% 0.09/0.27  % Model      : x86_64 x86_64
% 0.09/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.27  % Memory     : 8042.1875MB
% 0.09/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.27  % CPULimit   : 60
% 0.09/0.27  % DateTime   : Tue Dec  1 09:28:26 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.09/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.51  
% 3.65/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.51  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.65/1.51  
% 3.65/1.51  %Foreground sorts:
% 3.65/1.51  
% 3.65/1.51  
% 3.65/1.51  %Background operators:
% 3.65/1.51  
% 3.65/1.51  
% 3.65/1.51  %Foreground operators:
% 3.65/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.65/1.51  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.65/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.65/1.51  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.65/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.65/1.51  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.65/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.65/1.51  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.65/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.51  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.65/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.65/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.65/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.65/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.65/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.65/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.65/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.65/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.65/1.51  
% 3.65/1.53  tff(f_141, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 3.65/1.53  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.65/1.53  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.65/1.53  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 3.65/1.53  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 3.65/1.53  tff(f_44, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.65/1.53  tff(f_46, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.65/1.53  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.65/1.53  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.65/1.53  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.65/1.53  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.65/1.53  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.65/1.53  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 3.65/1.53  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.65/1.53  tff(c_58, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~v3_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.65/1.53  tff(c_76, plain, (~v3_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 3.65/1.53  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.65/1.53  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.65/1.53  tff(c_400, plain, (![B_109, A_110]: (v2_tops_1(B_109, A_110) | k1_tops_1(A_110, B_109)!=k1_xboole_0 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.65/1.53  tff(c_415, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_400])).
% 3.65/1.53  tff(c_425, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_415])).
% 3.65/1.53  tff(c_427, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_425])).
% 3.65/1.53  tff(c_483, plain, (![A_120, B_121]: (k1_tops_1(A_120, B_121)=k1_xboole_0 | ~v2_tops_1(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.65/1.53  tff(c_494, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_483])).
% 3.65/1.53  tff(c_503, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_494])).
% 3.65/1.53  tff(c_504, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_427, c_503])).
% 3.65/1.53  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.65/1.53  tff(c_64, plain, (v3_tops_1('#skF_3', '#skF_2') | k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.65/1.53  tff(c_77, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_76, c_64])).
% 3.65/1.53  tff(c_638, plain, (![B_134, A_135]: (v2_tops_1(B_134, A_135) | ~r1_tarski(B_134, k2_tops_1(A_135, B_134)) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.65/1.53  tff(c_649, plain, (v2_tops_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77, c_638])).
% 3.65/1.53  tff(c_656, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_12, c_649])).
% 3.65/1.53  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_504, c_656])).
% 3.65/1.53  tff(c_659, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_425])).
% 3.65/1.53  tff(c_52, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.65/1.53  tff(c_997, plain, (![B_165, A_166]: (v3_tops_1(B_165, A_166) | ~v4_pre_topc(B_165, A_166) | ~v2_tops_1(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.65/1.53  tff(c_1008, plain, (v3_tops_1('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_997])).
% 3.65/1.53  tff(c_1017, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_659, c_52, c_1008])).
% 3.65/1.53  tff(c_1019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1017])).
% 3.65/1.53  tff(c_1020, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_58])).
% 3.65/1.53  tff(c_16, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.65/1.53  tff(c_1098, plain, (![A_180, B_181]: (k2_xboole_0(k3_xboole_0(A_180, B_181), k4_xboole_0(A_180, B_181))=A_180)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.65/1.53  tff(c_1110, plain, (![A_182]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_182, k1_xboole_0))=A_182)), inference(superposition, [status(thm), theory('equality')], [c_16, c_1098])).
% 3.65/1.53  tff(c_22, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.65/1.53  tff(c_1022, plain, (![A_167, B_168]: (r1_tarski(A_167, B_168) | ~m1_subset_1(A_167, k1_zfmisc_1(B_168)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.65/1.53  tff(c_1030, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_22, c_1022])).
% 3.65/1.53  tff(c_1034, plain, (![A_170, B_171]: (k2_xboole_0(A_170, B_171)=B_171 | ~r1_tarski(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.65/1.53  tff(c_1045, plain, (![A_16]: (k2_xboole_0(k1_xboole_0, A_16)=A_16)), inference(resolution, [status(thm)], [c_1030, c_1034])).
% 3.65/1.53  tff(c_1116, plain, (![A_182]: (k4_xboole_0(A_182, k1_xboole_0)=A_182)), inference(superposition, [status(thm), theory('equality')], [c_1110, c_1045])).
% 3.65/1.53  tff(c_1207, plain, (![A_203, B_204, C_205]: (k7_subset_1(A_203, B_204, C_205)=k4_xboole_0(B_204, C_205) | ~m1_subset_1(B_204, k1_zfmisc_1(A_203)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.65/1.53  tff(c_1215, plain, (![C_205]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_205)=k4_xboole_0('#skF_3', C_205))), inference(resolution, [status(thm)], [c_54, c_1207])).
% 3.65/1.53  tff(c_1392, plain, (![A_234, B_235]: (k2_pre_topc(A_234, B_235)=B_235 | ~v4_pre_topc(B_235, A_234) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.65/1.53  tff(c_1403, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1392])).
% 3.65/1.53  tff(c_1412, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1403])).
% 3.65/1.53  tff(c_1021, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 3.65/1.53  tff(c_1217, plain, (![B_206, A_207]: (v2_tops_1(B_206, A_207) | ~v3_tops_1(B_206, A_207) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.65/1.53  tff(c_1224, plain, (v2_tops_1('#skF_3', '#skF_2') | ~v3_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1217])).
% 3.65/1.53  tff(c_1232, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1021, c_1224])).
% 3.65/1.53  tff(c_1437, plain, (![A_240, B_241]: (k1_tops_1(A_240, B_241)=k1_xboole_0 | ~v2_tops_1(B_241, A_240) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.65/1.53  tff(c_1448, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1437])).
% 3.65/1.53  tff(c_1457, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1232, c_1448])).
% 3.65/1.53  tff(c_1748, plain, (![A_260, B_261]: (k7_subset_1(u1_struct_0(A_260), k2_pre_topc(A_260, B_261), k1_tops_1(A_260, B_261))=k2_tops_1(A_260, B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_pre_topc(A_260))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.65/1.53  tff(c_1760, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), k1_xboole_0)=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1457, c_1748])).
% 3.65/1.53  tff(c_1769, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1116, c_1215, c_1412, c_1760])).
% 3.65/1.53  tff(c_1771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1020, c_1769])).
% 3.65/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.53  
% 3.65/1.53  Inference rules
% 3.65/1.53  ----------------------
% 3.65/1.53  #Ref     : 0
% 3.65/1.53  #Sup     : 376
% 3.65/1.53  #Fact    : 0
% 3.65/1.53  #Define  : 0
% 3.65/1.53  #Split   : 11
% 3.65/1.53  #Chain   : 0
% 3.65/1.53  #Close   : 0
% 3.65/1.53  
% 3.65/1.53  Ordering : KBO
% 3.65/1.53  
% 3.65/1.53  Simplification rules
% 3.65/1.53  ----------------------
% 3.65/1.53  #Subsume      : 29
% 3.65/1.53  #Demod        : 120
% 3.65/1.53  #Tautology    : 140
% 3.65/1.53  #SimpNegUnit  : 8
% 3.65/1.53  #BackRed      : 10
% 3.65/1.53  
% 3.65/1.53  #Partial instantiations: 0
% 3.65/1.53  #Strategies tried      : 1
% 3.65/1.53  
% 3.65/1.53  Timing (in seconds)
% 3.65/1.53  ----------------------
% 3.65/1.53  Preprocessing        : 0.36
% 3.65/1.53  Parsing              : 0.19
% 3.65/1.53  CNF conversion       : 0.02
% 3.65/1.53  Main loop            : 0.54
% 3.65/1.53  Inferencing          : 0.20
% 3.65/1.53  Reduction            : 0.16
% 3.65/1.53  Demodulation         : 0.11
% 3.65/1.53  BG Simplification    : 0.03
% 3.65/1.53  Subsumption          : 0.10
% 3.65/1.53  Abstraction          : 0.03
% 3.65/1.53  MUC search           : 0.00
% 3.65/1.53  Cooper               : 0.00
% 3.65/1.53  Total                : 0.94
% 3.65/1.53  Index Insertion      : 0.00
% 3.65/1.53  Index Deletion       : 0.00
% 3.65/1.53  Index Matching       : 0.00
% 3.65/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
