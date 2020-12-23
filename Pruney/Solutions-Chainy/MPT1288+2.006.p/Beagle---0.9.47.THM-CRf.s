%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:27 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.69s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 468 expanded)
%              Number of leaves         :   39 ( 172 expanded)
%              Depth                    :   20
%              Number of atoms          :  259 (1314 expanded)
%              Number of equality atoms :   36 ( 200 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tops_1 > v4_pre_topc > v3_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => k1_tops_1(A,k2_tops_1(A,B)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_143,axiom,(
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

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_165,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_tops_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_154,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => ( v3_tops_1(B,A)
            <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

tff(c_46,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_706,plain,(
    ! [A_105,B_106] :
      ( k7_subset_1(u1_struct_0(A_105),k2_pre_topc(A_105,B_106),k1_tops_1(A_105,B_106)) = k2_tops_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_153,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,k2_pre_topc(A_74,B_75)) = k2_pre_topc(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_153])).

tff(c_167,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_161])).

tff(c_349,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k1_tops_1(A_83,k2_pre_topc(A_83,B_84)),B_84)
      | ~ v4_tops_1(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_354,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_349])).

tff(c_357,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_354])).

tff(c_373,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_376,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_373])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_376])).

tff(c_382,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( k7_subset_1(A_3,B_4,C_5) = k4_xboole_0(B_4,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_421,plain,(
    ! [C_5] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_5) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_5) ),
    inference(resolution,[status(thm)],[c_382,c_8])).

tff(c_713,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_421])).

tff(c_741,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_713])).

tff(c_77,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,k2_pre_topc(A_61,B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_82,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_79])).

tff(c_48,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_20,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k1_tops_1(A_13,k2_pre_topc(A_13,B_15)),B_15)
      | ~ v4_tops_1(B_15,A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( v3_pre_topc(k1_tops_1(A_24,B_25),A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_393,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_382,c_30])).

tff(c_414,plain,(
    v3_pre_topc(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_393])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1336,plain,(
    ! [A_134,B_135] :
      ( k2_pre_topc(A_134,k2_pre_topc(A_134,k1_tops_1(A_134,B_135))) = k2_pre_topc(A_134,k1_tops_1(A_134,B_135))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_22,c_153])).

tff(c_1340,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_382,c_1336])).

tff(c_1358,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1340])).

tff(c_138,plain,(
    ! [A_72,B_73] :
      ( v4_pre_topc(k2_pre_topc(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_149,plain,(
    ! [A_6,B_7] :
      ( v4_pre_topc(k2_pre_topc(A_6,k2_pre_topc(A_6,B_7)),A_6)
      | ~ v2_pre_topc(A_6)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_138])).

tff(c_2517,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_149])).

tff(c_2545,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_2517])).

tff(c_6639,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2545])).

tff(c_6642,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_6639])).

tff(c_6646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_382,c_6642])).

tff(c_6648,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2545])).

tff(c_1042,plain,(
    ! [B_122,A_123,C_124] :
      ( r1_tarski(B_122,k1_tops_1(A_123,C_124))
      | ~ r1_tarski(B_122,C_124)
      | ~ v3_pre_topc(B_122,A_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1058,plain,(
    ! [B_122] :
      ( r1_tarski(B_122,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_122,'#skF_2')
      | ~ v3_pre_topc(B_122,'#skF_1')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_1042])).

tff(c_1076,plain,(
    ! [B_122] :
      ( r1_tarski(B_122,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_122,'#skF_2')
      | ~ v3_pre_topc(B_122,'#skF_1')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1058])).

tff(c_6676,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
    | ~ v3_pre_topc(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6648,c_1076])).

tff(c_6724,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_6676])).

tff(c_7051,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6724])).

tff(c_7054,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_7051])).

tff(c_7058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_7054])).

tff(c_7059,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6724])).

tff(c_827,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_tarski(k1_tops_1(A_108,B_109),k1_tops_1(A_108,C_110))
      | ~ r1_tarski(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_860,plain,(
    ! [A_108,C_110,B_109] :
      ( k1_tops_1(A_108,C_110) = k1_tops_1(A_108,B_109)
      | ~ r1_tarski(k1_tops_1(A_108,C_110),k1_tops_1(A_108,B_109))
      | ~ r1_tarski(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_827,c_2])).

tff(c_7072,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7059,c_860])).

tff(c_7077,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_382,c_82,c_7072])).

tff(c_738,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_706])).

tff(c_756,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_382,c_421,c_738])).

tff(c_7090,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7077,c_756])).

tff(c_7101,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_7090])).

tff(c_146,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_138])).

tff(c_152,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_146])).

tff(c_502,plain,(
    ! [A_88,B_89] :
      ( v3_tops_1(k2_tops_1(A_88,B_89),A_88)
      | ~ v4_pre_topc(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_504,plain,
    ( v3_tops_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_382,c_502])).

tff(c_519,plain,(
    v3_tops_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_152,c_504])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( v4_pre_topc(k2_tops_1(A_20,B_21),A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_395,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_382,c_26])).

tff(c_417,plain,(
    v4_pre_topc(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_395])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_256,plain,(
    ! [A_80,B_81] :
      ( k2_tops_1(A_80,B_81) = B_81
      | ~ v3_tops_1(B_81,A_80)
      | ~ v4_pre_topc(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4945,plain,(
    ! [A_191,B_192] :
      ( k2_tops_1(A_191,k2_tops_1(A_191,B_192)) = k2_tops_1(A_191,B_192)
      | ~ v3_tops_1(k2_tops_1(A_191,B_192),A_191)
      | ~ v4_pre_topc(k2_tops_1(A_191,B_192),A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_24,c_256])).

tff(c_4965,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ v3_tops_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_417,c_4945])).

tff(c_4999,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_382,c_519,c_4965])).

tff(c_34,plain,(
    ! [A_29,B_31] :
      ( k1_tops_1(A_29,k2_tops_1(A_29,k2_tops_1(A_29,B_31))) = k1_xboole_0
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_387,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_382,c_34])).

tff(c_405,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_387])).

tff(c_5104,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4999,c_405])).

tff(c_7353,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7101,c_5104])).

tff(c_7361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_7353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:54:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.51/2.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/2.99  
% 8.51/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/2.99  %$ v4_tops_1 > v4_pre_topc > v3_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.51/2.99  
% 8.51/2.99  %Foreground sorts:
% 8.51/2.99  
% 8.51/2.99  
% 8.51/2.99  %Background operators:
% 8.51/2.99  
% 8.51/2.99  
% 8.51/2.99  %Foreground operators:
% 8.51/2.99  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.51/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.51/2.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.51/2.99  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.51/2.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.51/2.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.51/2.99  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 8.51/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.51/2.99  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 8.51/2.99  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.51/2.99  tff('#skF_2', type, '#skF_2': $i).
% 8.51/2.99  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.51/2.99  tff('#skF_1', type, '#skF_1': $i).
% 8.51/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.51/2.99  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.51/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.51/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.51/2.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.51/2.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.51/2.99  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.51/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.51/2.99  
% 8.69/3.01  tff(f_177, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) => (k1_tops_1(A, k2_tops_1(A, B)) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tops_1)).
% 8.69/3.01  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 8.69/3.01  tff(f_41, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.69/3.01  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 8.69/3.01  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 8.69/3.01  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.69/3.01  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 8.69/3.01  tff(f_101, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 8.69/3.01  tff(f_71, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 8.69/3.01  tff(f_93, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 8.69/3.01  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 8.69/3.01  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 8.69/3.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.69/3.01  tff(f_165, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tops_1)).
% 8.69/3.01  tff(f_85, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_tops_1)).
% 8.69/3.01  tff(f_77, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.69/3.01  tff(f_154, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 8.69/3.01  tff(f_117, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l80_tops_1)).
% 8.69/3.01  tff(c_46, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.69/3.01  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.69/3.01  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.69/3.01  tff(c_706, plain, (![A_105, B_106]: (k7_subset_1(u1_struct_0(A_105), k2_pre_topc(A_105, B_106), k1_tops_1(A_105, B_106))=k2_tops_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.69/3.01  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k2_pre_topc(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.69/3.01  tff(c_153, plain, (![A_74, B_75]: (k2_pre_topc(A_74, k2_pre_topc(A_74, B_75))=k2_pre_topc(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.69/3.01  tff(c_161, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_153])).
% 8.69/3.01  tff(c_167, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_161])).
% 8.69/3.01  tff(c_349, plain, (![A_83, B_84]: (r1_tarski(k1_tops_1(A_83, k2_pre_topc(A_83, B_84)), B_84) | ~v4_tops_1(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.69/3.01  tff(c_354, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_167, c_349])).
% 8.69/3.01  tff(c_357, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_354])).
% 8.69/3.01  tff(c_373, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_357])).
% 8.69/3.01  tff(c_376, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_373])).
% 8.69/3.01  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_376])).
% 8.69/3.01  tff(c_382, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_357])).
% 8.69/3.01  tff(c_8, plain, (![A_3, B_4, C_5]: (k7_subset_1(A_3, B_4, C_5)=k4_xboole_0(B_4, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.69/3.01  tff(c_421, plain, (![C_5]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_5)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_5))), inference(resolution, [status(thm)], [c_382, c_8])).
% 8.69/3.01  tff(c_713, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_706, c_421])).
% 8.69/3.01  tff(c_741, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_713])).
% 8.69/3.01  tff(c_77, plain, (![B_60, A_61]: (r1_tarski(B_60, k2_pre_topc(A_61, B_60)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.69/3.01  tff(c_79, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_77])).
% 8.69/3.01  tff(c_82, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_79])).
% 8.69/3.01  tff(c_48, plain, (v4_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.69/3.01  tff(c_20, plain, (![A_13, B_15]: (r1_tarski(k1_tops_1(A_13, k2_pre_topc(A_13, B_15)), B_15) | ~v4_tops_1(B_15, A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.69/3.01  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.69/3.01  tff(c_30, plain, (![A_24, B_25]: (v3_pre_topc(k1_tops_1(A_24, B_25), A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.69/3.01  tff(c_393, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_382, c_30])).
% 8.69/3.01  tff(c_414, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_393])).
% 8.69/3.01  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.69/3.01  tff(c_1336, plain, (![A_134, B_135]: (k2_pre_topc(A_134, k2_pre_topc(A_134, k1_tops_1(A_134, B_135)))=k2_pre_topc(A_134, k1_tops_1(A_134, B_135)) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_22, c_153])).
% 8.69/3.01  tff(c_1340, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_382, c_1336])).
% 8.69/3.01  tff(c_1358, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1340])).
% 8.69/3.01  tff(c_138, plain, (![A_72, B_73]: (v4_pre_topc(k2_pre_topc(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.69/3.01  tff(c_149, plain, (![A_6, B_7]: (v4_pre_topc(k2_pre_topc(A_6, k2_pre_topc(A_6, B_7)), A_6) | ~v2_pre_topc(A_6) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_10, c_138])).
% 8.69/3.01  tff(c_2517, plain, (v4_pre_topc(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1358, c_149])).
% 8.69/3.01  tff(c_2545, plain, (v4_pre_topc(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_2517])).
% 8.69/3.01  tff(c_6639, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2545])).
% 8.69/3.01  tff(c_6642, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_6639])).
% 8.69/3.01  tff(c_6646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_382, c_6642])).
% 8.69/3.01  tff(c_6648, plain, (m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2545])).
% 8.69/3.01  tff(c_1042, plain, (![B_122, A_123, C_124]: (r1_tarski(B_122, k1_tops_1(A_123, C_124)) | ~r1_tarski(B_122, C_124) | ~v3_pre_topc(B_122, A_123) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.69/3.01  tff(c_1058, plain, (![B_122]: (r1_tarski(B_122, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_122, '#skF_2') | ~v3_pre_topc(B_122, '#skF_1') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_1042])).
% 8.69/3.01  tff(c_1076, plain, (![B_122]: (r1_tarski(B_122, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_122, '#skF_2') | ~v3_pre_topc(B_122, '#skF_1') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1058])).
% 8.69/3.01  tff(c_6676, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2') | ~v3_pre_topc(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_6648, c_1076])).
% 8.69/3.01  tff(c_6724, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_6676])).
% 8.69/3.01  tff(c_7051, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_6724])).
% 8.69/3.01  tff(c_7054, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_7051])).
% 8.69/3.01  tff(c_7058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_7054])).
% 8.69/3.01  tff(c_7059, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_6724])).
% 8.69/3.01  tff(c_827, plain, (![A_108, B_109, C_110]: (r1_tarski(k1_tops_1(A_108, B_109), k1_tops_1(A_108, C_110)) | ~r1_tarski(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.69/3.01  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.69/3.01  tff(c_860, plain, (![A_108, C_110, B_109]: (k1_tops_1(A_108, C_110)=k1_tops_1(A_108, B_109) | ~r1_tarski(k1_tops_1(A_108, C_110), k1_tops_1(A_108, B_109)) | ~r1_tarski(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_827, c_2])).
% 8.69/3.01  tff(c_7072, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7059, c_860])).
% 8.69/3.01  tff(c_7077, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_382, c_82, c_7072])).
% 8.69/3.01  tff(c_738, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_167, c_706])).
% 8.69/3.01  tff(c_756, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_382, c_421, c_738])).
% 8.69/3.01  tff(c_7090, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7077, c_756])).
% 8.69/3.01  tff(c_7101, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_741, c_7090])).
% 8.69/3.01  tff(c_146, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_138])).
% 8.69/3.01  tff(c_152, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_146])).
% 8.69/3.01  tff(c_502, plain, (![A_88, B_89]: (v3_tops_1(k2_tops_1(A_88, B_89), A_88) | ~v4_pre_topc(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.69/3.01  tff(c_504, plain, (v3_tops_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_382, c_502])).
% 8.69/3.01  tff(c_519, plain, (v3_tops_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_152, c_504])).
% 8.69/3.01  tff(c_26, plain, (![A_20, B_21]: (v4_pre_topc(k2_tops_1(A_20, B_21), A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.69/3.01  tff(c_395, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_382, c_26])).
% 8.69/3.01  tff(c_417, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_395])).
% 8.69/3.01  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(k2_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.69/3.01  tff(c_256, plain, (![A_80, B_81]: (k2_tops_1(A_80, B_81)=B_81 | ~v3_tops_1(B_81, A_80) | ~v4_pre_topc(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.69/3.01  tff(c_4945, plain, (![A_191, B_192]: (k2_tops_1(A_191, k2_tops_1(A_191, B_192))=k2_tops_1(A_191, B_192) | ~v3_tops_1(k2_tops_1(A_191, B_192), A_191) | ~v4_pre_topc(k2_tops_1(A_191, B_192), A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191))), inference(resolution, [status(thm)], [c_24, c_256])).
% 8.69/3.01  tff(c_4965, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~v3_tops_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_417, c_4945])).
% 8.69/3.01  tff(c_4999, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_382, c_519, c_4965])).
% 8.69/3.01  tff(c_34, plain, (![A_29, B_31]: (k1_tops_1(A_29, k2_tops_1(A_29, k2_tops_1(A_29, B_31)))=k1_xboole_0 | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.69/3.01  tff(c_387, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_382, c_34])).
% 8.69/3.01  tff(c_405, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_387])).
% 8.69/3.01  tff(c_5104, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4999, c_405])).
% 8.69/3.01  tff(c_7353, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7101, c_5104])).
% 8.69/3.01  tff(c_7361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_7353])).
% 8.69/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.69/3.01  
% 8.69/3.01  Inference rules
% 8.69/3.01  ----------------------
% 8.69/3.01  #Ref     : 0
% 8.69/3.01  #Sup     : 1546
% 8.69/3.01  #Fact    : 0
% 8.69/3.01  #Define  : 0
% 8.69/3.01  #Split   : 45
% 8.69/3.01  #Chain   : 0
% 8.69/3.01  #Close   : 0
% 8.69/3.01  
% 8.69/3.01  Ordering : KBO
% 8.69/3.01  
% 8.69/3.01  Simplification rules
% 8.69/3.01  ----------------------
% 8.69/3.01  #Subsume      : 152
% 8.69/3.01  #Demod        : 3088
% 8.69/3.01  #Tautology    : 611
% 8.69/3.01  #SimpNegUnit  : 32
% 8.69/3.01  #BackRed      : 31
% 8.69/3.01  
% 8.69/3.01  #Partial instantiations: 0
% 8.69/3.01  #Strategies tried      : 1
% 8.69/3.01  
% 8.69/3.01  Timing (in seconds)
% 8.69/3.01  ----------------------
% 8.69/3.01  Preprocessing        : 0.36
% 8.69/3.01  Parsing              : 0.20
% 8.69/3.01  CNF conversion       : 0.03
% 8.69/3.01  Main loop            : 1.87
% 8.69/3.01  Inferencing          : 0.44
% 8.69/3.01  Reduction            : 0.93
% 8.69/3.01  Demodulation         : 0.75
% 8.69/3.01  BG Simplification    : 0.06
% 8.69/3.01  Subsumption          : 0.35
% 8.69/3.01  Abstraction          : 0.07
% 8.69/3.01  MUC search           : 0.00
% 8.69/3.02  Cooper               : 0.00
% 8.69/3.02  Total                : 2.27
% 8.69/3.02  Index Insertion      : 0.00
% 8.69/3.02  Index Deletion       : 0.00
% 8.69/3.02  Index Matching       : 0.00
% 8.69/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
