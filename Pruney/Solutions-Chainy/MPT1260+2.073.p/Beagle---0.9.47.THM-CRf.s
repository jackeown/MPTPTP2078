%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:09 EST 2020

% Result     : Theorem 43.19s
% Output     : CNFRefutation 43.25s
% Verified   : 
% Statistics : Number of formulae       :  149 (1716 expanded)
%              Number of leaves         :   46 ( 580 expanded)
%              Depth                    :   17
%              Number of atoms          :  238 (3942 expanded)
%              Number of equality atoms :   69 ( 911 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_56,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_80,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1194,plain,(
    ! [A_160,B_161] :
      ( k4_subset_1(u1_struct_0(A_160),B_161,k2_tops_1(A_160,B_161)) = k2_pre_topc(A_160,B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1211,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1194])).

tff(c_1227,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1211])).

tff(c_40,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k2_tops_1(A_39,B_40),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1067,plain,(
    ! [A_157,B_158,C_159] :
      ( m1_subset_1(k4_subset_1(A_157,B_158,C_159),k1_zfmisc_1(A_157))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1966,plain,(
    ! [A_185,B_186,C_187] :
      ( r1_tarski(k4_subset_1(A_185,B_186,C_187),A_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(A_185))
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_185)) ) ),
    inference(resolution,[status(thm)],[c_1067,c_36])).

tff(c_1989,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1227,c_1966])).

tff(c_2010,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1989])).

tff(c_2017,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2010])).

tff(c_2020,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_2017])).

tff(c_2027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2020])).

tff(c_2029,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2010])).

tff(c_2127,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2029,c_36])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_854,plain,(
    ! [A_146,B_147,C_148] :
      ( k4_subset_1(A_146,B_147,C_148) = k2_xboole_0(B_147,C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2143,plain,(
    ! [B_189,B_190,A_191] :
      ( k4_subset_1(B_189,B_190,A_191) = k2_xboole_0(B_190,A_191)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(B_189))
      | ~ r1_tarski(A_191,B_189) ) ),
    inference(resolution,[status(thm)],[c_38,c_854])).

tff(c_2182,plain,(
    ! [A_192] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_192) = k2_xboole_0('#skF_3',A_192)
      | ~ r1_tarski(A_192,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_2143])).

tff(c_2185,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2127,c_2182])).

tff(c_2270,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1227,c_2185])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2332,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2270,c_12])).

tff(c_2028,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2010])).

tff(c_366,plain,(
    ! [A_106,B_107,C_108] :
      ( k7_subset_1(A_106,B_107,C_108) = k4_xboole_0(B_107,C_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_377,plain,(
    ! [B_38,A_37,C_108] :
      ( k7_subset_1(B_38,A_37,C_108) = k4_xboole_0(A_37,C_108)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_366])).

tff(c_2787,plain,(
    ! [C_199] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_199) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_199) ),
    inference(resolution,[status(thm)],[c_2028,c_377])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_134,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_64])).

tff(c_2797,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2787,c_134])).

tff(c_162,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k3_subset_1(A_86,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_198,plain,(
    ! [B_90,A_91] :
      ( k4_xboole_0(B_90,A_91) = k3_subset_1(B_90,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_38,c_162])).

tff(c_221,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),A_7) = k3_subset_1(k2_xboole_0(A_7,B_8),A_7) ),
    inference(resolution,[status(thm)],[c_12,c_198])).

tff(c_2323,plain,(
    k3_subset_1(k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')),'#skF_3') = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2270,c_221])).

tff(c_2338,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2270,c_2323])).

tff(c_2814,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2797,c_2338])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2897,plain,
    ( m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2814,c_18])).

tff(c_85644,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2897])).

tff(c_85647,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_85644])).

tff(c_85651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_85647])).

tff(c_85653,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2897])).

tff(c_280,plain,(
    ! [A_101,B_102] :
      ( k3_subset_1(A_101,k3_subset_1(A_101,B_102)) = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_291,plain,(
    ! [B_38,A_37] :
      ( k3_subset_1(B_38,k3_subset_1(B_38,A_37)) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_280])).

tff(c_2891,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2814,c_291])).

tff(c_2903,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2891])).

tff(c_378,plain,(
    ! [C_108] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_108) = k4_xboole_0('#skF_3',C_108) ),
    inference(resolution,[status(thm)],[c_52,c_366])).

tff(c_1378,plain,(
    ! [A_163,B_164] :
      ( k7_subset_1(u1_struct_0(A_163),B_164,k2_tops_1(A_163,B_164)) = k1_tops_1(A_163,B_164)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1397,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1378])).

tff(c_1416,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_378,c_1397])).

tff(c_433,plain,(
    ! [B_112,A_113,C_114] :
      ( k7_subset_1(B_112,A_113,C_114) = k4_xboole_0(A_113,C_114)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_38,c_366])).

tff(c_459,plain,(
    ! [A_7,B_8,C_114] : k7_subset_1(k2_xboole_0(A_7,B_8),A_7,C_114) = k4_xboole_0(A_7,C_114) ),
    inference(resolution,[status(thm)],[c_12,c_433])).

tff(c_2326,plain,(
    ! [C_114] : k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',C_114) = k4_xboole_0('#skF_3',C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2270,c_459])).

tff(c_22,plain,(
    ! [A_18] : m1_subset_1('#skF_1'(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(A_79,B_80,B_80) = B_80
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_148,plain,(
    ! [A_79,B_80] : k9_subset_1(A_79,B_80,B_80) = B_80 ),
    inference(resolution,[status(thm)],[c_22,c_139])).

tff(c_1496,plain,(
    ! [A_165,B_166,C_167] :
      ( k9_subset_1(A_165,B_166,k3_subset_1(A_165,C_167)) = k7_subset_1(A_165,B_166,C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(A_165))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8668,plain,(
    ! [A_313,B_314,B_315] :
      ( k9_subset_1(A_313,B_314,k3_subset_1(A_313,k3_subset_1(A_313,B_315))) = k7_subset_1(A_313,B_314,k3_subset_1(A_313,B_315))
      | ~ m1_subset_1(B_314,k1_zfmisc_1(A_313))
      | ~ m1_subset_1(B_315,k1_zfmisc_1(A_313)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1496])).

tff(c_115666,plain,(
    ! [A_1008,B_1009] :
      ( k7_subset_1(A_1008,k3_subset_1(A_1008,k3_subset_1(A_1008,B_1009)),k3_subset_1(A_1008,B_1009)) = k3_subset_1(A_1008,k3_subset_1(A_1008,B_1009))
      | ~ m1_subset_1(k3_subset_1(A_1008,k3_subset_1(A_1008,B_1009)),k1_zfmisc_1(A_1008))
      | ~ m1_subset_1(B_1009,k1_zfmisc_1(A_1008)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_8668])).

tff(c_115722,plain,
    ( k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2814,c_115666])).

tff(c_115773,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85653,c_85653,c_2903,c_1416,c_2326,c_2903,c_2814,c_2814,c_2903,c_2814,c_115722])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_1437,plain,
    ( k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1416,c_119])).

tff(c_1448,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1416,c_1437])).

tff(c_1479,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1448])).

tff(c_115822,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115773,c_1479])).

tff(c_115855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_115822])).

tff(c_115856,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1448])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_739,plain,(
    ! [A_136,B_137] :
      ( v3_pre_topc(k1_tops_1(A_136,B_137),A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_749,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_739])).

tff(c_758,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_749])).

tff(c_115861,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115856,c_758])).

tff(c_115865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_115861])).

tff(c_115866,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_116202,plain,(
    ! [A_1049,B_1050,C_1051] :
      ( k7_subset_1(A_1049,B_1050,C_1051) = k4_xboole_0(B_1050,C_1051)
      | ~ m1_subset_1(B_1050,k1_zfmisc_1(A_1049)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_116214,plain,(
    ! [C_1051] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_1051) = k4_xboole_0('#skF_3',C_1051) ),
    inference(resolution,[status(thm)],[c_52,c_116202])).

tff(c_117002,plain,(
    ! [A_1110,B_1111] :
      ( k7_subset_1(u1_struct_0(A_1110),B_1111,k2_tops_1(A_1110,B_1111)) = k1_tops_1(A_1110,B_1111)
      | ~ m1_subset_1(B_1111,k1_zfmisc_1(u1_struct_0(A_1110)))
      | ~ l1_pre_topc(A_1110) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_117017,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_117002])).

tff(c_117030,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_116214,c_117017])).

tff(c_115893,plain,(
    ! [B_1015,A_1016] :
      ( B_1015 = A_1016
      | ~ r1_tarski(B_1015,A_1016)
      | ~ r1_tarski(A_1016,B_1015) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115907,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_115893])).

tff(c_117054,plain,
    ( k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_117030,c_115907])).

tff(c_117066,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117030,c_117054])).

tff(c_117097,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_117066])).

tff(c_115867,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_117549,plain,(
    ! [B_1122,A_1123,C_1124] :
      ( r1_tarski(B_1122,k1_tops_1(A_1123,C_1124))
      | ~ r1_tarski(B_1122,C_1124)
      | ~ v3_pre_topc(B_1122,A_1123)
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(u1_struct_0(A_1123)))
      | ~ m1_subset_1(B_1122,k1_zfmisc_1(u1_struct_0(A_1123)))
      | ~ l1_pre_topc(A_1123) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_117570,plain,(
    ! [B_1122] :
      ( r1_tarski(B_1122,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1122,'#skF_3')
      | ~ v3_pre_topc(B_1122,'#skF_2')
      | ~ m1_subset_1(B_1122,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_117549])).

tff(c_117595,plain,(
    ! [B_1125] :
      ( r1_tarski(B_1125,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1125,'#skF_3')
      | ~ v3_pre_topc(B_1125,'#skF_2')
      | ~ m1_subset_1(B_1125,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_117570])).

tff(c_117626,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_117595])).

tff(c_117643,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115867,c_6,c_117626])).

tff(c_117645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117097,c_117643])).

tff(c_117646,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_117066])).

tff(c_117948,plain,(
    ! [A_1133,B_1134] :
      ( k7_subset_1(u1_struct_0(A_1133),k2_pre_topc(A_1133,B_1134),k1_tops_1(A_1133,B_1134)) = k2_tops_1(A_1133,B_1134)
      | ~ m1_subset_1(B_1134,k1_zfmisc_1(u1_struct_0(A_1133)))
      | ~ l1_pre_topc(A_1133) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_117957,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_117646,c_117948])).

tff(c_117961,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_117957])).

tff(c_117963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115866,c_117961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:17:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.19/33.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.25/33.58  
% 43.25/33.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.25/33.58  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 43.25/33.58  
% 43.25/33.58  %Foreground sorts:
% 43.25/33.58  
% 43.25/33.58  
% 43.25/33.58  %Background operators:
% 43.25/33.58  
% 43.25/33.58  
% 43.25/33.58  %Foreground operators:
% 43.25/33.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 43.25/33.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.25/33.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 43.25/33.58  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 43.25/33.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 43.25/33.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 43.25/33.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 43.25/33.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.25/33.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 43.25/33.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 43.25/33.58  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 43.25/33.58  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 43.25/33.58  tff('#skF_2', type, '#skF_2': $i).
% 43.25/33.58  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 43.25/33.58  tff('#skF_3', type, '#skF_3': $i).
% 43.25/33.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 43.25/33.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.25/33.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.25/33.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 43.25/33.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 43.25/33.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 43.25/33.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 43.25/33.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 43.25/33.58  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 43.25/33.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 43.25/33.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 43.25/33.58  
% 43.25/33.60  tff(f_148, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 43.25/33.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 43.25/33.60  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 43.25/33.60  tff(f_93, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 43.25/33.60  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 43.25/33.60  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 43.25/33.60  tff(f_70, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 43.25/33.60  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 43.25/33.60  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 43.25/33.60  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 43.25/33.60  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 43.25/33.60  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 43.25/33.60  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 43.25/33.60  tff(f_56, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 43.25/33.60  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 43.25/33.60  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 43.25/33.60  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 43.25/33.60  tff(f_101, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 43.25/33.60  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 43.25/33.60  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 43.25/33.60  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 43.25/33.60  tff(c_80, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 43.25/33.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.25/33.60  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 43.25/33.60  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 43.25/33.60  tff(c_1194, plain, (![A_160, B_161]: (k4_subset_1(u1_struct_0(A_160), B_161, k2_tops_1(A_160, B_161))=k2_pre_topc(A_160, B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_129])).
% 43.25/33.60  tff(c_1211, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1194])).
% 43.25/33.60  tff(c_1227, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1211])).
% 43.25/33.60  tff(c_40, plain, (![A_39, B_40]: (m1_subset_1(k2_tops_1(A_39, B_40), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_93])).
% 43.25/33.60  tff(c_1067, plain, (![A_157, B_158, C_159]: (m1_subset_1(k4_subset_1(A_157, B_158, C_159), k1_zfmisc_1(A_157)) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 43.25/33.60  tff(c_36, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 43.25/33.60  tff(c_1966, plain, (![A_185, B_186, C_187]: (r1_tarski(k4_subset_1(A_185, B_186, C_187), A_185) | ~m1_subset_1(C_187, k1_zfmisc_1(A_185)) | ~m1_subset_1(B_186, k1_zfmisc_1(A_185)))), inference(resolution, [status(thm)], [c_1067, c_36])).
% 43.25/33.60  tff(c_1989, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1227, c_1966])).
% 43.25/33.60  tff(c_2010, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1989])).
% 43.25/33.60  tff(c_2017, plain, (~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2010])).
% 43.25/33.60  tff(c_2020, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_2017])).
% 43.25/33.60  tff(c_2027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2020])).
% 43.25/33.60  tff(c_2029, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_2010])).
% 43.25/33.60  tff(c_2127, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2029, c_36])).
% 43.25/33.60  tff(c_38, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_87])).
% 43.25/33.60  tff(c_854, plain, (![A_146, B_147, C_148]: (k4_subset_1(A_146, B_147, C_148)=k2_xboole_0(B_147, C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 43.25/33.60  tff(c_2143, plain, (![B_189, B_190, A_191]: (k4_subset_1(B_189, B_190, A_191)=k2_xboole_0(B_190, A_191) | ~m1_subset_1(B_190, k1_zfmisc_1(B_189)) | ~r1_tarski(A_191, B_189))), inference(resolution, [status(thm)], [c_38, c_854])).
% 43.25/33.60  tff(c_2182, plain, (![A_192]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_192)=k2_xboole_0('#skF_3', A_192) | ~r1_tarski(A_192, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_52, c_2143])).
% 43.25/33.60  tff(c_2185, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2127, c_2182])).
% 43.25/33.60  tff(c_2270, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1227, c_2185])).
% 43.25/33.60  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 43.25/33.60  tff(c_2332, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2270, c_12])).
% 43.25/33.60  tff(c_2028, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2010])).
% 43.25/33.60  tff(c_366, plain, (![A_106, B_107, C_108]: (k7_subset_1(A_106, B_107, C_108)=k4_xboole_0(B_107, C_108) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 43.25/33.60  tff(c_377, plain, (![B_38, A_37, C_108]: (k7_subset_1(B_38, A_37, C_108)=k4_xboole_0(A_37, C_108) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_38, c_366])).
% 43.25/33.60  tff(c_2787, plain, (![C_199]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_199)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_199))), inference(resolution, [status(thm)], [c_2028, c_377])).
% 43.25/33.60  tff(c_64, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 43.25/33.60  tff(c_134, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_64])).
% 43.25/33.60  tff(c_2797, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2787, c_134])).
% 43.25/33.60  tff(c_162, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k3_subset_1(A_86, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.25/33.60  tff(c_198, plain, (![B_90, A_91]: (k4_xboole_0(B_90, A_91)=k3_subset_1(B_90, A_91) | ~r1_tarski(A_91, B_90))), inference(resolution, [status(thm)], [c_38, c_162])).
% 43.25/33.60  tff(c_221, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), A_7)=k3_subset_1(k2_xboole_0(A_7, B_8), A_7))), inference(resolution, [status(thm)], [c_12, c_198])).
% 43.25/33.60  tff(c_2323, plain, (k3_subset_1(k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3')), '#skF_3')=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2270, c_221])).
% 43.25/33.60  tff(c_2338, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2270, c_2323])).
% 43.25/33.60  tff(c_2814, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2797, c_2338])).
% 43.25/33.60  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(k3_subset_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 43.25/33.60  tff(c_2897, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2814, c_18])).
% 43.25/33.60  tff(c_85644, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2897])).
% 43.25/33.60  tff(c_85647, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_85644])).
% 43.25/33.60  tff(c_85651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2332, c_85647])).
% 43.25/33.60  tff(c_85653, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2897])).
% 43.25/33.60  tff(c_280, plain, (![A_101, B_102]: (k3_subset_1(A_101, k3_subset_1(A_101, B_102))=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 43.25/33.60  tff(c_291, plain, (![B_38, A_37]: (k3_subset_1(B_38, k3_subset_1(B_38, A_37))=A_37 | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_38, c_280])).
% 43.25/33.60  tff(c_2891, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2814, c_291])).
% 43.25/33.60  tff(c_2903, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2891])).
% 43.25/33.60  tff(c_378, plain, (![C_108]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_108)=k4_xboole_0('#skF_3', C_108))), inference(resolution, [status(thm)], [c_52, c_366])).
% 43.25/33.60  tff(c_1378, plain, (![A_163, B_164]: (k7_subset_1(u1_struct_0(A_163), B_164, k2_tops_1(A_163, B_164))=k1_tops_1(A_163, B_164) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_136])).
% 43.25/33.60  tff(c_1397, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1378])).
% 43.25/33.60  tff(c_1416, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_378, c_1397])).
% 43.25/33.60  tff(c_433, plain, (![B_112, A_113, C_114]: (k7_subset_1(B_112, A_113, C_114)=k4_xboole_0(A_113, C_114) | ~r1_tarski(A_113, B_112))), inference(resolution, [status(thm)], [c_38, c_366])).
% 43.25/33.60  tff(c_459, plain, (![A_7, B_8, C_114]: (k7_subset_1(k2_xboole_0(A_7, B_8), A_7, C_114)=k4_xboole_0(A_7, C_114))), inference(resolution, [status(thm)], [c_12, c_433])).
% 43.25/33.60  tff(c_2326, plain, (![C_114]: (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', C_114)=k4_xboole_0('#skF_3', C_114))), inference(superposition, [status(thm), theory('equality')], [c_2270, c_459])).
% 43.25/33.60  tff(c_22, plain, (![A_18]: (m1_subset_1('#skF_1'(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 43.25/33.60  tff(c_139, plain, (![A_79, B_80, C_81]: (k9_subset_1(A_79, B_80, B_80)=B_80 | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 43.25/33.60  tff(c_148, plain, (![A_79, B_80]: (k9_subset_1(A_79, B_80, B_80)=B_80)), inference(resolution, [status(thm)], [c_22, c_139])).
% 43.25/33.60  tff(c_1496, plain, (![A_165, B_166, C_167]: (k9_subset_1(A_165, B_166, k3_subset_1(A_165, C_167))=k7_subset_1(A_165, B_166, C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(A_165)) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 43.25/33.60  tff(c_8668, plain, (![A_313, B_314, B_315]: (k9_subset_1(A_313, B_314, k3_subset_1(A_313, k3_subset_1(A_313, B_315)))=k7_subset_1(A_313, B_314, k3_subset_1(A_313, B_315)) | ~m1_subset_1(B_314, k1_zfmisc_1(A_313)) | ~m1_subset_1(B_315, k1_zfmisc_1(A_313)))), inference(resolution, [status(thm)], [c_18, c_1496])).
% 43.25/33.60  tff(c_115666, plain, (![A_1008, B_1009]: (k7_subset_1(A_1008, k3_subset_1(A_1008, k3_subset_1(A_1008, B_1009)), k3_subset_1(A_1008, B_1009))=k3_subset_1(A_1008, k3_subset_1(A_1008, B_1009)) | ~m1_subset_1(k3_subset_1(A_1008, k3_subset_1(A_1008, B_1009)), k1_zfmisc_1(A_1008)) | ~m1_subset_1(B_1009, k1_zfmisc_1(A_1008)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_8668])).
% 43.25/33.60  tff(c_115722, plain, (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3'))=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')) | ~m1_subset_1(k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2814, c_115666])).
% 43.25/33.60  tff(c_115773, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85653, c_85653, c_2903, c_1416, c_2326, c_2903, c_2814, c_2814, c_2903, c_2814, c_115722])).
% 43.25/33.60  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 43.25/33.60  tff(c_105, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.25/33.60  tff(c_119, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_105])).
% 43.25/33.60  tff(c_1437, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1416, c_119])).
% 43.25/33.60  tff(c_1448, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1416, c_1437])).
% 43.25/33.60  tff(c_1479, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1448])).
% 43.25/33.60  tff(c_115822, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_115773, c_1479])).
% 43.25/33.60  tff(c_115855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_115822])).
% 43.25/33.60  tff(c_115856, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1448])).
% 43.25/33.60  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 43.25/33.60  tff(c_739, plain, (![A_136, B_137]: (v3_pre_topc(k1_tops_1(A_136, B_137), A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_101])).
% 43.25/33.60  tff(c_749, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_739])).
% 43.25/33.60  tff(c_758, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_749])).
% 43.25/33.60  tff(c_115861, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115856, c_758])).
% 43.25/33.60  tff(c_115865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_115861])).
% 43.25/33.60  tff(c_115866, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 43.25/33.60  tff(c_116202, plain, (![A_1049, B_1050, C_1051]: (k7_subset_1(A_1049, B_1050, C_1051)=k4_xboole_0(B_1050, C_1051) | ~m1_subset_1(B_1050, k1_zfmisc_1(A_1049)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 43.25/33.60  tff(c_116214, plain, (![C_1051]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_1051)=k4_xboole_0('#skF_3', C_1051))), inference(resolution, [status(thm)], [c_52, c_116202])).
% 43.25/33.60  tff(c_117002, plain, (![A_1110, B_1111]: (k7_subset_1(u1_struct_0(A_1110), B_1111, k2_tops_1(A_1110, B_1111))=k1_tops_1(A_1110, B_1111) | ~m1_subset_1(B_1111, k1_zfmisc_1(u1_struct_0(A_1110))) | ~l1_pre_topc(A_1110))), inference(cnfTransformation, [status(thm)], [f_136])).
% 43.25/33.60  tff(c_117017, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_117002])).
% 43.25/33.60  tff(c_117030, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_116214, c_117017])).
% 43.25/33.60  tff(c_115893, plain, (![B_1015, A_1016]: (B_1015=A_1016 | ~r1_tarski(B_1015, A_1016) | ~r1_tarski(A_1016, B_1015))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.25/33.60  tff(c_115907, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_115893])).
% 43.25/33.60  tff(c_117054, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117030, c_115907])).
% 43.25/33.60  tff(c_117066, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_117030, c_117054])).
% 43.25/33.60  tff(c_117097, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_117066])).
% 43.25/33.60  tff(c_115867, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 43.25/33.60  tff(c_117549, plain, (![B_1122, A_1123, C_1124]: (r1_tarski(B_1122, k1_tops_1(A_1123, C_1124)) | ~r1_tarski(B_1122, C_1124) | ~v3_pre_topc(B_1122, A_1123) | ~m1_subset_1(C_1124, k1_zfmisc_1(u1_struct_0(A_1123))) | ~m1_subset_1(B_1122, k1_zfmisc_1(u1_struct_0(A_1123))) | ~l1_pre_topc(A_1123))), inference(cnfTransformation, [status(thm)], [f_122])).
% 43.25/33.60  tff(c_117570, plain, (![B_1122]: (r1_tarski(B_1122, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1122, '#skF_3') | ~v3_pre_topc(B_1122, '#skF_2') | ~m1_subset_1(B_1122, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_117549])).
% 43.25/33.60  tff(c_117595, plain, (![B_1125]: (r1_tarski(B_1125, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1125, '#skF_3') | ~v3_pre_topc(B_1125, '#skF_2') | ~m1_subset_1(B_1125, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_117570])).
% 43.25/33.60  tff(c_117626, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_117595])).
% 43.25/33.60  tff(c_117643, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_115867, c_6, c_117626])).
% 43.25/33.60  tff(c_117645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117097, c_117643])).
% 43.25/33.60  tff(c_117646, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_117066])).
% 43.25/33.60  tff(c_117948, plain, (![A_1133, B_1134]: (k7_subset_1(u1_struct_0(A_1133), k2_pre_topc(A_1133, B_1134), k1_tops_1(A_1133, B_1134))=k2_tops_1(A_1133, B_1134) | ~m1_subset_1(B_1134, k1_zfmisc_1(u1_struct_0(A_1133))) | ~l1_pre_topc(A_1133))), inference(cnfTransformation, [status(thm)], [f_108])).
% 43.25/33.60  tff(c_117957, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_117646, c_117948])).
% 43.25/33.60  tff(c_117961, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_117957])).
% 43.25/33.60  tff(c_117963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115866, c_117961])).
% 43.25/33.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.25/33.60  
% 43.25/33.60  Inference rules
% 43.25/33.60  ----------------------
% 43.25/33.60  #Ref     : 0
% 43.25/33.60  #Sup     : 27428
% 43.25/33.60  #Fact    : 0
% 43.25/33.60  #Define  : 0
% 43.25/33.60  #Split   : 28
% 43.25/33.60  #Chain   : 0
% 43.25/33.60  #Close   : 0
% 43.25/33.60  
% 43.25/33.60  Ordering : KBO
% 43.25/33.60  
% 43.25/33.60  Simplification rules
% 43.25/33.60  ----------------------
% 43.25/33.60  #Subsume      : 914
% 43.25/33.60  #Demod        : 38392
% 43.25/33.60  #Tautology    : 11562
% 43.25/33.60  #SimpNegUnit  : 9
% 43.25/33.60  #BackRed      : 160
% 43.25/33.60  
% 43.25/33.60  #Partial instantiations: 0
% 43.25/33.60  #Strategies tried      : 1
% 43.25/33.60  
% 43.25/33.60  Timing (in seconds)
% 43.25/33.60  ----------------------
% 43.25/33.60  Preprocessing        : 0.36
% 43.25/33.60  Parsing              : 0.20
% 43.25/33.60  CNF conversion       : 0.02
% 43.25/33.60  Main loop            : 32.44
% 43.25/33.60  Inferencing          : 3.77
% 43.25/33.60  Reduction            : 19.92
% 43.25/33.60  Demodulation         : 17.98
% 43.25/33.60  BG Simplification    : 0.41
% 43.25/33.61  Subsumption          : 7.02
% 43.25/33.61  Abstraction          : 0.83
% 43.25/33.61  MUC search           : 0.00
% 43.25/33.61  Cooper               : 0.00
% 43.25/33.61  Total                : 32.85
% 43.25/33.61  Index Insertion      : 0.00
% 43.25/33.61  Index Deletion       : 0.00
% 43.25/33.61  Index Matching       : 0.00
% 43.25/33.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
