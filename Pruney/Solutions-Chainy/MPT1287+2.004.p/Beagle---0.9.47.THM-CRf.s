%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:26 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 242 expanded)
%              Number of leaves         :   29 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          :  169 ( 660 expanded)
%              Number of equality atoms :   18 (  58 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v6_tops_1(B,A)
                    & v6_tops_1(C,A) )
                 => v6_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v5_tops_1(B,A)
                  & v5_tops_1(C,A) )
               => v5_tops_1(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_37,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_150,plain,(
    ! [A_50,B_51,C_52] :
      ( k9_subset_1(A_50,B_51,C_52) = k3_xboole_0(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [B_51] : k9_subset_1(u1_struct_0('#skF_1'),B_51,'#skF_3') = k3_xboole_0(B_51,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_24,plain,(
    ~ v6_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_172,plain,(
    ~ v6_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_24])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k3_subset_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [A_42,B_43] :
      ( k3_subset_1(A_42,k3_subset_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_278,plain,(
    ! [B_64,A_65] :
      ( v6_tops_1(B_64,A_65)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_65),B_64),A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_292,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_278])).

tff(c_296,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_292])).

tff(c_400,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_403,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4,c_400])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_403])).

tff(c_412,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_61,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_289,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_278])).

tff(c_294,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_289])).

tff(c_854,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_857,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4,c_854])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_857])).

tff(c_866,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_14,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_428,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_412,c_14])).

tff(c_28,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_59,plain,(
    ! [B_20,A_19] :
      ( k3_subset_1(B_20,k3_subset_1(B_20,A_19)) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_16,c_52])).

tff(c_377,plain,(
    ! [A_74,B_75] :
      ( v5_tops_1(k3_subset_1(u1_struct_0(A_74),B_75),A_74)
      | ~ v6_tops_1(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3895,plain,(
    ! [A_182,A_183] :
      ( v5_tops_1(A_182,A_183)
      | ~ v6_tops_1(k3_subset_1(u1_struct_0(A_183),A_182),A_183)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_183),A_182),k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183)
      | ~ r1_tarski(A_182,u1_struct_0(A_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_377])).

tff(c_3943,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3895])).

tff(c_3976,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_34,c_32,c_28,c_60,c_3943])).

tff(c_900,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_866,c_14])).

tff(c_26,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3940,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')),'#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_3895])).

tff(c_3974,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_34,c_30,c_26,c_61,c_3940])).

tff(c_429,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(A_76,B_77,k3_subset_1(A_76,C_78)) = k7_subset_1(A_76,B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_671,plain,(
    ! [B_98,B_99,A_100] :
      ( k9_subset_1(B_98,B_99,k3_subset_1(B_98,A_100)) = k7_subset_1(B_98,B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(B_98))
      | ~ r1_tarski(A_100,B_98) ) ),
    inference(resolution,[status(thm)],[c_16,c_429])).

tff(c_756,plain,(
    ! [A_105] :
      ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),A_105)) = k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_105)
      | ~ r1_tarski(A_105,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_671])).

tff(c_803,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_756])).

tff(c_823,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_803])).

tff(c_1591,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_823])).

tff(c_545,plain,(
    ! [A_83,B_84,C_85] :
      ( k4_subset_1(A_83,k3_subset_1(A_83,B_84),C_85) = k3_subset_1(A_83,k7_subset_1(A_83,B_84,C_85))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2143,plain,(
    ! [A_144,B_145,B_146] :
      ( k4_subset_1(A_144,k3_subset_1(A_144,B_145),k3_subset_1(A_144,B_146)) = k3_subset_1(A_144,k7_subset_1(A_144,B_145,k3_subset_1(A_144,B_146)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_144))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_4,c_545])).

tff(c_22,plain,(
    ! [A_24,B_28,C_30] :
      ( v5_tops_1(k4_subset_1(u1_struct_0(A_24),B_28,C_30),A_24)
      | ~ v5_tops_1(C_30,A_24)
      | ~ v5_tops_1(B_28,A_24)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11367,plain,(
    ! [A_267,B_268,B_269] :
      ( v5_tops_1(k3_subset_1(u1_struct_0(A_267),k7_subset_1(u1_struct_0(A_267),B_268,k3_subset_1(u1_struct_0(A_267),B_269))),A_267)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_267),B_269),A_267)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_267),B_268),A_267)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_267),B_269),k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_267),B_268),k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_267))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2143,c_22])).

tff(c_11489,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k3_xboole_0('#skF_2','#skF_3')),'#skF_1')
    | ~ v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1591,c_11367])).

tff(c_11579,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k3_xboole_0('#skF_2','#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_36,c_34,c_412,c_866,c_3976,c_3974,c_11489])).

tff(c_18,plain,(
    ! [B_23,A_21] :
      ( v6_tops_1(B_23,A_21)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_21),B_23),A_21)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11600,plain,
    ( v6_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_11579,c_18])).

tff(c_11603,plain,
    ( v6_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_11600])).

tff(c_11604,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_11603])).

tff(c_11608,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_11604])).

tff(c_11611,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_11608])).

tff(c_11615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_11611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:22:40 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.50/3.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.50/3.95  
% 11.50/3.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.50/3.95  %$ v6_tops_1 > v5_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 11.50/3.95  
% 11.50/3.95  %Foreground sorts:
% 11.50/3.95  
% 11.50/3.95  
% 11.50/3.95  %Background operators:
% 11.50/3.95  
% 11.50/3.95  
% 11.50/3.95  %Foreground operators:
% 11.50/3.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.50/3.95  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 11.50/3.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.50/3.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.50/3.95  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.50/3.95  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.50/3.95  tff('#skF_2', type, '#skF_2': $i).
% 11.50/3.95  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.50/3.95  tff('#skF_3', type, '#skF_3': $i).
% 11.50/3.95  tff('#skF_1', type, '#skF_1': $i).
% 11.50/3.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.50/3.95  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 11.50/3.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.50/3.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.50/3.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.50/3.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.50/3.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.50/3.95  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.50/3.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.50/3.95  
% 11.59/3.97  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v6_tops_1(B, A) & v6_tops_1(C, A)) => v6_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_tops_1)).
% 11.59/3.97  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.59/3.97  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 11.59/3.97  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.59/3.97  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.59/3.97  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.59/3.97  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> v5_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_tops_1)).
% 11.59/3.97  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 11.59/3.97  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 11.59/3.97  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v5_tops_1(B, A) & v5_tops_1(C, A)) => v5_tops_1(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_tops_1)).
% 11.59/3.97  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.59/3.97  tff(c_37, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.59/3.97  tff(c_44, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_37])).
% 11.59/3.97  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.59/3.97  tff(c_16, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.59/3.97  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.59/3.97  tff(c_150, plain, (![A_50, B_51, C_52]: (k9_subset_1(A_50, B_51, C_52)=k3_xboole_0(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.59/3.97  tff(c_162, plain, (![B_51]: (k9_subset_1(u1_struct_0('#skF_1'), B_51, '#skF_3')=k3_xboole_0(B_51, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_150])).
% 11.59/3.97  tff(c_24, plain, (~v6_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.59/3.97  tff(c_172, plain, (~v6_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_24])).
% 11.59/3.97  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.59/3.97  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.59/3.97  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k3_subset_1(A_4, B_5), k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.59/3.97  tff(c_52, plain, (![A_42, B_43]: (k3_subset_1(A_42, k3_subset_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.59/3.97  tff(c_60, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_52])).
% 11.59/3.97  tff(c_278, plain, (![B_64, A_65]: (v6_tops_1(B_64, A_65) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_65), B_64), A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.59/3.97  tff(c_292, plain, (v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_60, c_278])).
% 11.59/3.97  tff(c_296, plain, (v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_292])).
% 11.59/3.97  tff(c_400, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_296])).
% 11.59/3.97  tff(c_403, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_4, c_400])).
% 11.59/3.97  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_403])).
% 11.59/3.97  tff(c_412, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_296])).
% 11.59/3.97  tff(c_61, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_30, c_52])).
% 11.59/3.97  tff(c_289, plain, (v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v5_tops_1('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_278])).
% 11.59/3.97  tff(c_294, plain, (v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v5_tops_1('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_289])).
% 11.59/3.97  tff(c_854, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_294])).
% 11.59/3.97  tff(c_857, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_4, c_854])).
% 11.59/3.97  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_857])).
% 11.59/3.97  tff(c_866, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_294])).
% 11.59/3.97  tff(c_14, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.59/3.97  tff(c_428, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_412, c_14])).
% 11.59/3.97  tff(c_28, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.59/3.97  tff(c_59, plain, (![B_20, A_19]: (k3_subset_1(B_20, k3_subset_1(B_20, A_19))=A_19 | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_16, c_52])).
% 11.59/3.97  tff(c_377, plain, (![A_74, B_75]: (v5_tops_1(k3_subset_1(u1_struct_0(A_74), B_75), A_74) | ~v6_tops_1(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.59/3.97  tff(c_3895, plain, (![A_182, A_183]: (v5_tops_1(A_182, A_183) | ~v6_tops_1(k3_subset_1(u1_struct_0(A_183), A_182), A_183) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_183), A_182), k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183) | ~r1_tarski(A_182, u1_struct_0(A_183)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_377])).
% 11.59/3.97  tff(c_3943, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_3895])).
% 11.59/3.97  tff(c_3976, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_34, c_32, c_28, c_60, c_3943])).
% 11.59/3.97  tff(c_900, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_866, c_14])).
% 11.59/3.97  tff(c_26, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.59/3.97  tff(c_3940, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_3895])).
% 11.59/3.97  tff(c_3974, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_900, c_34, c_30, c_26, c_61, c_3940])).
% 11.59/3.97  tff(c_429, plain, (![A_76, B_77, C_78]: (k9_subset_1(A_76, B_77, k3_subset_1(A_76, C_78))=k7_subset_1(A_76, B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.59/3.97  tff(c_671, plain, (![B_98, B_99, A_100]: (k9_subset_1(B_98, B_99, k3_subset_1(B_98, A_100))=k7_subset_1(B_98, B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(B_98)) | ~r1_tarski(A_100, B_98))), inference(resolution, [status(thm)], [c_16, c_429])).
% 11.59/3.97  tff(c_756, plain, (![A_105]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), A_105))=k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_105) | ~r1_tarski(A_105, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_671])).
% 11.59/3.97  tff(c_803, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_756])).
% 11.59/3.97  tff(c_823, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_803])).
% 11.59/3.97  tff(c_1591, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_900, c_823])).
% 11.59/3.97  tff(c_545, plain, (![A_83, B_84, C_85]: (k4_subset_1(A_83, k3_subset_1(A_83, B_84), C_85)=k3_subset_1(A_83, k7_subset_1(A_83, B_84, C_85)) | ~m1_subset_1(C_85, k1_zfmisc_1(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.59/3.97  tff(c_2143, plain, (![A_144, B_145, B_146]: (k4_subset_1(A_144, k3_subset_1(A_144, B_145), k3_subset_1(A_144, B_146))=k3_subset_1(A_144, k7_subset_1(A_144, B_145, k3_subset_1(A_144, B_146))) | ~m1_subset_1(B_145, k1_zfmisc_1(A_144)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_144)))), inference(resolution, [status(thm)], [c_4, c_545])).
% 11.59/3.97  tff(c_22, plain, (![A_24, B_28, C_30]: (v5_tops_1(k4_subset_1(u1_struct_0(A_24), B_28, C_30), A_24) | ~v5_tops_1(C_30, A_24) | ~v5_tops_1(B_28, A_24) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.59/3.97  tff(c_11367, plain, (![A_267, B_268, B_269]: (v5_tops_1(k3_subset_1(u1_struct_0(A_267), k7_subset_1(u1_struct_0(A_267), B_268, k3_subset_1(u1_struct_0(A_267), B_269))), A_267) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_267), B_269), A_267) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_267), B_268), A_267) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_267), B_269), k1_zfmisc_1(u1_struct_0(A_267))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_267), B_268), k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_267))) | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0(A_267))))), inference(superposition, [status(thm), theory('equality')], [c_2143, c_22])).
% 11.59/3.97  tff(c_11489, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k3_xboole_0('#skF_2', '#skF_3')), '#skF_1') | ~v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1591, c_11367])).
% 11.59/3.97  tff(c_11579, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k3_xboole_0('#skF_2', '#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_36, c_34, c_412, c_866, c_3976, c_3974, c_11489])).
% 11.59/3.97  tff(c_18, plain, (![B_23, A_21]: (v6_tops_1(B_23, A_21) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_21), B_23), A_21) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.59/3.97  tff(c_11600, plain, (v6_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_11579, c_18])).
% 11.59/3.97  tff(c_11603, plain, (v6_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_11600])).
% 11.59/3.97  tff(c_11604, plain, (~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_172, c_11603])).
% 11.59/3.97  tff(c_11608, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_11604])).
% 11.59/3.97  tff(c_11611, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_11608])).
% 11.59/3.97  tff(c_11615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_11611])).
% 11.59/3.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/3.97  
% 11.59/3.97  Inference rules
% 11.59/3.97  ----------------------
% 11.59/3.97  #Ref     : 0
% 11.59/3.97  #Sup     : 2791
% 11.59/3.97  #Fact    : 0
% 11.59/3.97  #Define  : 0
% 11.59/3.97  #Split   : 17
% 11.59/3.97  #Chain   : 0
% 11.59/3.97  #Close   : 0
% 11.59/3.97  
% 11.59/3.97  Ordering : KBO
% 11.59/3.97  
% 11.59/3.97  Simplification rules
% 11.59/3.97  ----------------------
% 11.59/3.97  #Subsume      : 253
% 11.59/3.97  #Demod        : 2742
% 11.59/3.97  #Tautology    : 710
% 11.59/3.97  #SimpNegUnit  : 28
% 11.59/3.97  #BackRed      : 19
% 11.59/3.97  
% 11.59/3.97  #Partial instantiations: 0
% 11.59/3.97  #Strategies tried      : 1
% 11.59/3.97  
% 11.59/3.97  Timing (in seconds)
% 11.59/3.97  ----------------------
% 11.59/3.97  Preprocessing        : 0.37
% 11.59/3.97  Parsing              : 0.19
% 11.59/3.97  CNF conversion       : 0.03
% 11.59/3.97  Main loop            : 2.83
% 11.59/3.97  Inferencing          : 0.86
% 11.59/3.97  Reduction            : 1.15
% 11.59/3.97  Demodulation         : 0.90
% 11.59/3.97  BG Simplification    : 0.11
% 11.59/3.97  Subsumption          : 0.57
% 11.59/3.97  Abstraction          : 0.18
% 11.59/3.97  MUC search           : 0.00
% 11.59/3.97  Cooper               : 0.00
% 11.59/3.97  Total                : 3.24
% 11.59/3.97  Index Insertion      : 0.00
% 11.59/3.97  Index Deletion       : 0.00
% 11.59/3.97  Index Matching       : 0.00
% 11.59/3.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
