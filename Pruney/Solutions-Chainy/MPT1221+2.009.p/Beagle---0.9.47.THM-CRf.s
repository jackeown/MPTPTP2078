%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:24 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 359 expanded)
%              Number of leaves         :   37 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  202 ( 835 expanded)
%              Number of equality atoms :   30 ( 126 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_225,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_162,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_173,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_211,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( k2_struct_0(A) = k4_subset_1(u1_struct_0(A),B,C)
                  & r1_xboole_0(B,C) )
               => C = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

tff(f_180,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_subset_1(u1_struct_0(A),k2_struct_0(A),k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_84,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_110,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_82,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_80,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_90,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_147,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_90])).

tff(c_64,plain,(
    ! [A_55] :
      ( l1_struct_0(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_504,plain,(
    ! [A_143,B_144] :
      ( k3_subset_1(A_143,k3_subset_1(A_143,B_144)) = B_144
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_525,plain,(
    k3_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_80,c_504])).

tff(c_1074,plain,(
    ! [B_192,C_193,A_194] :
      ( r1_xboole_0(B_192,C_193)
      | ~ r1_tarski(B_192,k3_subset_1(A_194,C_193))
      | ~ m1_subset_1(C_193,k1_zfmisc_1(A_194))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(A_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1088,plain,(
    ! [B_192] :
      ( r1_xboole_0(B_192,k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r1_tarski(B_192,'#skF_5')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_1074])).

tff(c_1156,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1088])).

tff(c_1205,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_10,c_1156])).

tff(c_1215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1205])).

tff(c_1217,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1088])).

tff(c_6546,plain,(
    ! [A_464,B_465] :
      ( k4_subset_1(u1_struct_0(A_464),B_465,k3_subset_1(u1_struct_0(A_464),B_465)) = k2_struct_0(A_464)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_464)))
      | ~ l1_struct_0(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_6562,plain,
    ( k4_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') = k2_struct_0('#skF_4')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_6546])).

tff(c_6574,plain,
    ( k4_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') = k2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1217,c_6562])).

tff(c_6612,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6574])).

tff(c_6615,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_6612])).

tff(c_6619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6615])).

tff(c_6621,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6574])).

tff(c_36,plain,(
    ! [A_27,B_28,C_32] :
      ( r2_hidden('#skF_3'(A_27,B_28,C_32),B_28)
      | r1_tarski(B_28,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6305,plain,(
    ! [A_454,B_455,C_456] :
      ( ~ r2_hidden('#skF_3'(A_454,B_455,C_456),C_456)
      | r1_tarski(B_455,C_456)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(A_454))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(A_454)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6316,plain,(
    ! [B_457,A_458] :
      ( r1_tarski(B_457,B_457)
      | ~ m1_subset_1(B_457,k1_zfmisc_1(A_458)) ) ),
    inference(resolution,[status(thm)],[c_36,c_6305])).

tff(c_6358,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_1217,c_6316])).

tff(c_28,plain,(
    ! [B_23,C_25,A_22] :
      ( r1_xboole_0(B_23,C_25)
      | ~ r1_tarski(B_23,k3_subset_1(A_22,C_25))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6437,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_6358,c_28])).

tff(c_6448,plain,(
    r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1217,c_80,c_6437])).

tff(c_6620,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6574])).

tff(c_7334,plain,(
    ! [A_520,B_521,C_522] :
      ( k7_subset_1(u1_struct_0(A_520),k2_struct_0(A_520),B_521) = C_522
      | ~ r1_xboole_0(B_521,C_522)
      | k4_subset_1(u1_struct_0(A_520),B_521,C_522) != k2_struct_0(A_520)
      | ~ m1_subset_1(C_522,k1_zfmisc_1(u1_struct_0(A_520)))
      | ~ m1_subset_1(B_521,k1_zfmisc_1(u1_struct_0(A_520)))
      | ~ l1_struct_0(A_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_7336,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6620,c_7334])).

tff(c_7341,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6621,c_1217,c_80,c_6448,c_7336])).

tff(c_70,plain,(
    ! [A_60,B_62] :
      ( k7_subset_1(u1_struct_0(A_60),k2_struct_0(A_60),k7_subset_1(u1_struct_0(A_60),k2_struct_0(A_60),B_62)) = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_7346,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5') = k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7341,c_70])).

tff(c_7358,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5') = k3_subset_1(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6621,c_1217,c_7346])).

tff(c_56,plain,(
    ! [B_51,A_49] :
      ( v4_pre_topc(B_51,A_49)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_49),k2_struct_0(A_49),B_51),A_49)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_7385,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7358,c_56])).

tff(c_7396,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_147,c_7385])).

tff(c_7398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_7396])).

tff(c_7399,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_7400,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_8024,plain,(
    ! [A_612,B_613] :
      ( k3_subset_1(A_612,k3_subset_1(A_612,B_613)) = B_613
      | ~ m1_subset_1(B_613,k1_zfmisc_1(A_612)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8048,plain,(
    k3_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_80,c_8024])).

tff(c_11143,plain,(
    ! [A_823,B_824] :
      ( k4_subset_1(u1_struct_0(A_823),B_824,k3_subset_1(u1_struct_0(A_823),B_824)) = k2_struct_0(A_823)
      | ~ m1_subset_1(B_824,k1_zfmisc_1(u1_struct_0(A_823)))
      | ~ l1_struct_0(A_823) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_11156,plain,
    ( k4_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') = k2_struct_0('#skF_4')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8048,c_11143])).

tff(c_11197,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11156])).

tff(c_11200,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_11197])).

tff(c_11204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_11200])).

tff(c_11206,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_11156])).

tff(c_8666,plain,(
    ! [B_659,A_660,C_661] :
      ( r1_tarski(B_659,k3_subset_1(A_660,C_661))
      | ~ r1_xboole_0(B_659,C_661)
      | ~ m1_subset_1(C_661,k1_zfmisc_1(A_660))
      | ~ m1_subset_1(B_659,k1_zfmisc_1(A_660)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8674,plain,(
    ! [B_659] :
      ( r1_tarski(B_659,'#skF_5')
      | ~ r1_xboole_0(B_659,k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8048,c_8666])).

tff(c_10890,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_8674])).

tff(c_10901,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_10,c_10890])).

tff(c_10914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10901])).

tff(c_10916,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_8674])).

tff(c_10922,plain,(
    ! [B_810,C_811,A_812] :
      ( r1_xboole_0(B_810,C_811)
      | ~ r1_tarski(B_810,k3_subset_1(A_812,C_811))
      | ~ m1_subset_1(C_811,k1_zfmisc_1(A_812))
      | ~ m1_subset_1(B_810,k1_zfmisc_1(A_812)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10935,plain,(
    ! [B_810] :
      ( r1_xboole_0(B_810,k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r1_tarski(B_810,'#skF_5')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_810,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8048,c_10922])).

tff(c_11017,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_10935])).

tff(c_11133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10916,c_11017])).

tff(c_11135,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_10935])).

tff(c_11879,plain,(
    ! [A_877,B_878,C_879] :
      ( ~ r2_hidden('#skF_3'(A_877,B_878,C_879),C_879)
      | r1_tarski(B_878,C_879)
      | ~ m1_subset_1(C_879,k1_zfmisc_1(A_877))
      | ~ m1_subset_1(B_878,k1_zfmisc_1(A_877)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_11890,plain,(
    ! [B_880,A_881] :
      ( r1_tarski(B_880,B_880)
      | ~ m1_subset_1(B_880,k1_zfmisc_1(A_881)) ) ),
    inference(resolution,[status(thm)],[c_36,c_11879])).

tff(c_11926,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_11135,c_11890])).

tff(c_11961,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_11926,c_28])).

tff(c_11972,plain,(
    r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11135,c_80,c_11961])).

tff(c_11205,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | k4_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_11156])).

tff(c_11708,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11135,c_11205])).

tff(c_12579,plain,(
    ! [A_928,B_929,C_930] :
      ( k7_subset_1(u1_struct_0(A_928),k2_struct_0(A_928),B_929) = C_930
      | ~ r1_xboole_0(B_929,C_930)
      | k4_subset_1(u1_struct_0(A_928),B_929,C_930) != k2_struct_0(A_928)
      | ~ m1_subset_1(C_930,k1_zfmisc_1(u1_struct_0(A_928)))
      | ~ m1_subset_1(B_929,k1_zfmisc_1(u1_struct_0(A_928)))
      | ~ l1_struct_0(A_928) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_12581,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11708,c_12579])).

tff(c_12586,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11206,c_11135,c_80,c_11972,c_12581])).

tff(c_12591,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5') = k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12586,c_70])).

tff(c_12603,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'),'#skF_5') = k3_subset_1(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11206,c_11135,c_12591])).

tff(c_58,plain,(
    ! [A_49,B_51] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_49),k2_struct_0(A_49),B_51),A_49)
      | ~ v4_pre_topc(B_51,A_49)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_12620,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12603,c_58])).

tff(c_12631,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_7400,c_12620])).

tff(c_12633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7399,c_12631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.93/2.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.93/2.91  
% 7.93/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.93/2.91  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 7.93/2.91  
% 7.93/2.91  %Foreground sorts:
% 7.93/2.91  
% 7.93/2.91  
% 7.93/2.91  %Background operators:
% 7.93/2.91  
% 7.93/2.91  
% 7.93/2.91  %Foreground operators:
% 7.93/2.91  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.93/2.91  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.93/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.93/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.93/2.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.93/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.93/2.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.93/2.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.93/2.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.93/2.91  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.93/2.91  tff('#skF_5', type, '#skF_5': $i).
% 7.93/2.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.93/2.91  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.93/2.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.93/2.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.93/2.91  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.93/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.93/2.91  tff('#skF_4', type, '#skF_4': $i).
% 7.93/2.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.93/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.93/2.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.93/2.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.93/2.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.93/2.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.93/2.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.93/2.91  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.93/2.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.93/2.91  
% 7.93/2.93  tff(f_225, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 7.93/2.93  tff(f_162, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.93/2.93  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.93/2.93  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.93/2.93  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 7.93/2.93  tff(f_173, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_pre_topc)).
% 7.93/2.93  tff(f_103, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 7.93/2.93  tff(f_211, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((k2_struct_0(A) = k4_subset_1(u1_struct_0(A), B, C)) & r1_xboole_0(B, C)) => (C = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_pre_topc)).
% 7.93/2.93  tff(f_180, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_subset_1(u1_struct_0(A), k2_struct_0(A), k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 7.93/2.93  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 7.93/2.93  tff(c_84, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.93/2.93  tff(c_110, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 7.93/2.93  tff(c_82, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.93/2.93  tff(c_80, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.93/2.93  tff(c_90, plain, (v4_pre_topc('#skF_5', '#skF_4') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.93/2.93  tff(c_147, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_110, c_90])).
% 7.93/2.93  tff(c_64, plain, (![A_55]: (l1_struct_0(A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.93/2.93  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.93/2.93  tff(c_504, plain, (![A_143, B_144]: (k3_subset_1(A_143, k3_subset_1(A_143, B_144))=B_144 | ~m1_subset_1(B_144, k1_zfmisc_1(A_143)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.93/2.93  tff(c_525, plain, (k3_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_80, c_504])).
% 7.93/2.93  tff(c_1074, plain, (![B_192, C_193, A_194]: (r1_xboole_0(B_192, C_193) | ~r1_tarski(B_192, k3_subset_1(A_194, C_193)) | ~m1_subset_1(C_193, k1_zfmisc_1(A_194)) | ~m1_subset_1(B_192, k1_zfmisc_1(A_194)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.93/2.93  tff(c_1088, plain, (![B_192]: (r1_xboole_0(B_192, k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')) | ~r1_tarski(B_192, '#skF_5') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_525, c_1074])).
% 7.93/2.93  tff(c_1156, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1088])).
% 7.93/2.93  tff(c_1205, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_1156])).
% 7.93/2.93  tff(c_1215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_1205])).
% 7.93/2.93  tff(c_1217, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1088])).
% 7.93/2.93  tff(c_6546, plain, (![A_464, B_465]: (k4_subset_1(u1_struct_0(A_464), B_465, k3_subset_1(u1_struct_0(A_464), B_465))=k2_struct_0(A_464) | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0(A_464))) | ~l1_struct_0(A_464))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.93/2.93  tff(c_6562, plain, (k4_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5')=k2_struct_0('#skF_4') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_525, c_6546])).
% 7.93/2.93  tff(c_6574, plain, (k4_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5')=k2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1217, c_6562])).
% 7.93/2.93  tff(c_6612, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_6574])).
% 7.93/2.93  tff(c_6615, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_6612])).
% 7.93/2.93  tff(c_6619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_6615])).
% 7.93/2.93  tff(c_6621, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_6574])).
% 7.93/2.93  tff(c_36, plain, (![A_27, B_28, C_32]: (r2_hidden('#skF_3'(A_27, B_28, C_32), B_28) | r1_tarski(B_28, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.93/2.93  tff(c_6305, plain, (![A_454, B_455, C_456]: (~r2_hidden('#skF_3'(A_454, B_455, C_456), C_456) | r1_tarski(B_455, C_456) | ~m1_subset_1(C_456, k1_zfmisc_1(A_454)) | ~m1_subset_1(B_455, k1_zfmisc_1(A_454)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.93/2.93  tff(c_6316, plain, (![B_457, A_458]: (r1_tarski(B_457, B_457) | ~m1_subset_1(B_457, k1_zfmisc_1(A_458)))), inference(resolution, [status(thm)], [c_36, c_6305])).
% 7.93/2.93  tff(c_6358, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_1217, c_6316])).
% 7.93/2.93  tff(c_28, plain, (![B_23, C_25, A_22]: (r1_xboole_0(B_23, C_25) | ~r1_tarski(B_23, k3_subset_1(A_22, C_25)) | ~m1_subset_1(C_25, k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.93/2.93  tff(c_6437, plain, (r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6358, c_28])).
% 7.93/2.93  tff(c_6448, plain, (r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1217, c_80, c_6437])).
% 7.93/2.93  tff(c_6620, plain, (k4_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5')=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_6574])).
% 7.93/2.93  tff(c_7334, plain, (![A_520, B_521, C_522]: (k7_subset_1(u1_struct_0(A_520), k2_struct_0(A_520), B_521)=C_522 | ~r1_xboole_0(B_521, C_522) | k4_subset_1(u1_struct_0(A_520), B_521, C_522)!=k2_struct_0(A_520) | ~m1_subset_1(C_522, k1_zfmisc_1(u1_struct_0(A_520))) | ~m1_subset_1(B_521, k1_zfmisc_1(u1_struct_0(A_520))) | ~l1_struct_0(A_520))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.93/2.93  tff(c_7336, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6620, c_7334])).
% 7.93/2.93  tff(c_7341, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6621, c_1217, c_80, c_6448, c_7336])).
% 7.93/2.93  tff(c_70, plain, (![A_60, B_62]: (k7_subset_1(u1_struct_0(A_60), k2_struct_0(A_60), k7_subset_1(u1_struct_0(A_60), k2_struct_0(A_60), B_62))=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.93/2.93  tff(c_7346, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5')=k3_subset_1(u1_struct_0('#skF_4'), '#skF_5') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7341, c_70])).
% 7.93/2.93  tff(c_7358, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5')=k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6621, c_1217, c_7346])).
% 7.93/2.93  tff(c_56, plain, (![B_51, A_49]: (v4_pre_topc(B_51, A_49) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_49), k2_struct_0(A_49), B_51), A_49) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.93/2.93  tff(c_7385, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7358, c_56])).
% 7.93/2.93  tff(c_7396, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_147, c_7385])).
% 7.93/2.93  tff(c_7398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_7396])).
% 7.93/2.93  tff(c_7399, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 7.93/2.93  tff(c_7400, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 7.93/2.93  tff(c_8024, plain, (![A_612, B_613]: (k3_subset_1(A_612, k3_subset_1(A_612, B_613))=B_613 | ~m1_subset_1(B_613, k1_zfmisc_1(A_612)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.93/2.93  tff(c_8048, plain, (k3_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_80, c_8024])).
% 7.93/2.93  tff(c_11143, plain, (![A_823, B_824]: (k4_subset_1(u1_struct_0(A_823), B_824, k3_subset_1(u1_struct_0(A_823), B_824))=k2_struct_0(A_823) | ~m1_subset_1(B_824, k1_zfmisc_1(u1_struct_0(A_823))) | ~l1_struct_0(A_823))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.93/2.93  tff(c_11156, plain, (k4_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5')=k2_struct_0('#skF_4') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8048, c_11143])).
% 7.93/2.93  tff(c_11197, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_11156])).
% 7.93/2.93  tff(c_11200, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_11197])).
% 7.93/2.93  tff(c_11204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_11200])).
% 7.93/2.93  tff(c_11206, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_11156])).
% 7.93/2.93  tff(c_8666, plain, (![B_659, A_660, C_661]: (r1_tarski(B_659, k3_subset_1(A_660, C_661)) | ~r1_xboole_0(B_659, C_661) | ~m1_subset_1(C_661, k1_zfmisc_1(A_660)) | ~m1_subset_1(B_659, k1_zfmisc_1(A_660)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.93/2.93  tff(c_8674, plain, (![B_659]: (r1_tarski(B_659, '#skF_5') | ~r1_xboole_0(B_659, k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_8048, c_8666])).
% 7.93/2.93  tff(c_10890, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_8674])).
% 7.93/2.93  tff(c_10901, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_10890])).
% 7.93/2.93  tff(c_10914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_10901])).
% 7.93/2.93  tff(c_10916, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_8674])).
% 7.93/2.93  tff(c_10922, plain, (![B_810, C_811, A_812]: (r1_xboole_0(B_810, C_811) | ~r1_tarski(B_810, k3_subset_1(A_812, C_811)) | ~m1_subset_1(C_811, k1_zfmisc_1(A_812)) | ~m1_subset_1(B_810, k1_zfmisc_1(A_812)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.93/2.93  tff(c_10935, plain, (![B_810]: (r1_xboole_0(B_810, k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')) | ~r1_tarski(B_810, '#skF_5') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_810, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_8048, c_10922])).
% 7.93/2.93  tff(c_11017, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_10935])).
% 7.93/2.93  tff(c_11133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10916, c_11017])).
% 7.93/2.93  tff(c_11135, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_10935])).
% 7.93/2.93  tff(c_11879, plain, (![A_877, B_878, C_879]: (~r2_hidden('#skF_3'(A_877, B_878, C_879), C_879) | r1_tarski(B_878, C_879) | ~m1_subset_1(C_879, k1_zfmisc_1(A_877)) | ~m1_subset_1(B_878, k1_zfmisc_1(A_877)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.93/2.93  tff(c_11890, plain, (![B_880, A_881]: (r1_tarski(B_880, B_880) | ~m1_subset_1(B_880, k1_zfmisc_1(A_881)))), inference(resolution, [status(thm)], [c_36, c_11879])).
% 7.93/2.93  tff(c_11926, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_11135, c_11890])).
% 7.93/2.93  tff(c_11961, plain, (r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_11926, c_28])).
% 7.93/2.93  tff(c_11972, plain, (r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11135, c_80, c_11961])).
% 7.93/2.93  tff(c_11205, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | k4_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5')=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_11156])).
% 7.93/2.93  tff(c_11708, plain, (k4_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11135, c_11205])).
% 7.93/2.93  tff(c_12579, plain, (![A_928, B_929, C_930]: (k7_subset_1(u1_struct_0(A_928), k2_struct_0(A_928), B_929)=C_930 | ~r1_xboole_0(B_929, C_930) | k4_subset_1(u1_struct_0(A_928), B_929, C_930)!=k2_struct_0(A_928) | ~m1_subset_1(C_930, k1_zfmisc_1(u1_struct_0(A_928))) | ~m1_subset_1(B_929, k1_zfmisc_1(u1_struct_0(A_928))) | ~l1_struct_0(A_928))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.93/2.93  tff(c_12581, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~r1_xboole_0(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11708, c_12579])).
% 7.93/2.93  tff(c_12586, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11206, c_11135, c_80, c_11972, c_12581])).
% 7.93/2.93  tff(c_12591, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5')=k3_subset_1(u1_struct_0('#skF_4'), '#skF_5') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12586, c_70])).
% 7.93/2.93  tff(c_12603, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_4'), '#skF_5')=k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11206, c_11135, c_12591])).
% 7.93/2.93  tff(c_58, plain, (![A_49, B_51]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_49), k2_struct_0(A_49), B_51), A_49) | ~v4_pre_topc(B_51, A_49) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.93/2.93  tff(c_12620, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v4_pre_topc('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12603, c_58])).
% 7.93/2.93  tff(c_12631, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_7400, c_12620])).
% 7.93/2.93  tff(c_12633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7399, c_12631])).
% 7.93/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.93/2.93  
% 7.93/2.93  Inference rules
% 7.93/2.93  ----------------------
% 7.93/2.93  #Ref     : 0
% 7.93/2.93  #Sup     : 2874
% 7.93/2.93  #Fact    : 0
% 7.93/2.93  #Define  : 0
% 7.93/2.93  #Split   : 52
% 7.93/2.93  #Chain   : 0
% 7.93/2.93  #Close   : 0
% 7.93/2.93  
% 7.93/2.93  Ordering : KBO
% 7.93/2.93  
% 7.93/2.93  Simplification rules
% 7.93/2.93  ----------------------
% 7.93/2.93  #Subsume      : 570
% 7.93/2.93  #Demod        : 1497
% 7.93/2.93  #Tautology    : 1085
% 7.93/2.93  #SimpNegUnit  : 67
% 7.93/2.93  #BackRed      : 181
% 7.93/2.93  
% 7.93/2.93  #Partial instantiations: 0
% 7.93/2.93  #Strategies tried      : 1
% 7.93/2.93  
% 7.93/2.93  Timing (in seconds)
% 7.93/2.93  ----------------------
% 7.93/2.93  Preprocessing        : 0.37
% 7.93/2.93  Parsing              : 0.20
% 7.93/2.93  CNF conversion       : 0.03
% 7.93/2.93  Main loop            : 1.77
% 7.93/2.93  Inferencing          : 0.59
% 7.93/2.93  Reduction            : 0.59
% 7.93/2.93  Demodulation         : 0.39
% 7.93/2.93  BG Simplification    : 0.07
% 7.93/2.93  Subsumption          : 0.36
% 7.93/2.93  Abstraction          : 0.09
% 7.93/2.94  MUC search           : 0.00
% 7.93/2.94  Cooper               : 0.00
% 7.93/2.94  Total                : 2.18
% 7.93/2.94  Index Insertion      : 0.00
% 7.93/2.94  Index Deletion       : 0.00
% 7.93/2.94  Index Matching       : 0.00
% 7.93/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
