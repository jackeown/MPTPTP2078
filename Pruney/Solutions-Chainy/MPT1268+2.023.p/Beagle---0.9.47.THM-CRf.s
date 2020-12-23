%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:49 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 132 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  159 ( 377 expanded)
%              Number of equality atoms :   30 (  63 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_78,axiom,(
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

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_57,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_294,plain,(
    ! [B_63,A_64] :
      ( v2_tops_1(B_63,A_64)
      | k1_tops_1(A_64,B_63) != k1_xboole_0
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_301,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_294])).

tff(c_305,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_301])).

tff(c_306,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_305])).

tff(c_232,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_tops_1(A_59,B_60),B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_237,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_232])).

tff(c_241,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_237])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_434,plain,(
    ! [A_74,B_75] :
      ( v3_pre_topc(k1_tops_1(A_74,B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_439,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_434])).

tff(c_443,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_439])).

tff(c_58,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_148,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_162,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_54,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_62,c_148])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [C_35] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_35
      | ~ v3_pre_topc(C_35,'#skF_1')
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_272,plain,(
    ! [C_62] :
      ( k1_xboole_0 = C_62
      | ~ v3_pre_topc(C_62,'#skF_1')
      | ~ r1_tarski(C_62,'#skF_2')
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_54])).

tff(c_691,plain,(
    ! [A_87] :
      ( k1_xboole_0 = A_87
      | ~ v3_pre_topc(A_87,'#skF_1')
      | ~ r1_tarski(A_87,'#skF_2')
      | ~ r1_tarski(A_87,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_272])).

tff(c_735,plain,(
    ! [A_88] :
      ( k1_xboole_0 = A_88
      | ~ v3_pre_topc(A_88,'#skF_1')
      | ~ r1_tarski(A_88,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_162,c_691])).

tff(c_738,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_443,c_735])).

tff(c_741,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_738])).

tff(c_743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_741])).

tff(c_744,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_750,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = k1_xboole_0
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_758,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_750])).

tff(c_807,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(k4_xboole_0(A_98,C_99),B_100)
      | ~ r1_tarski(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_824,plain,(
    ! [B_101,B_102] :
      ( r1_tarski(k1_xboole_0,B_101)
      | ~ r1_tarski(B_102,B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_807])).

tff(c_853,plain,(
    ! [B_103] : r1_tarski(k1_xboole_0,B_103) ),
    inference(resolution,[status(thm)],[c_6,c_824])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_857,plain,(
    ! [B_103] : k4_xboole_0(k1_xboole_0,B_103) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_853,c_10])).

tff(c_745,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_749,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_38])).

tff(c_40,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_747,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_40])).

tff(c_42,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_771,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_42])).

tff(c_1135,plain,(
    ! [A_120,B_121] :
      ( k1_tops_1(A_120,B_121) = k1_xboole_0
      | ~ v2_tops_1(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1145,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1135])).

tff(c_1152,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_745,c_1145])).

tff(c_1693,plain,(
    ! [B_144,A_145,C_146] :
      ( r1_tarski(B_144,k1_tops_1(A_145,C_146))
      | ~ r1_tarski(B_144,C_146)
      | ~ v3_pre_topc(B_144,A_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1700,plain,(
    ! [B_144] :
      ( r1_tarski(B_144,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_144,'#skF_2')
      | ~ v3_pre_topc(B_144,'#skF_1')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1693])).

tff(c_1883,plain,(
    ! [B_152] :
      ( r1_tarski(B_152,k1_xboole_0)
      | ~ r1_tarski(B_152,'#skF_2')
      | ~ v3_pre_topc(B_152,'#skF_1')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1152,c_1700])).

tff(c_1890,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_771,c_1883])).

tff(c_1897,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_747,c_1890])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_869,plain,(
    ! [B_104,A_105] :
      ( B_104 = A_105
      | ~ r1_tarski(B_104,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_888,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_869])).

tff(c_1903,plain,
    ( k1_xboole_0 = '#skF_3'
    | k4_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1897,c_888])).

tff(c_1922,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_1903])).

tff(c_1924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_1922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:32:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.59  
% 3.41/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.59  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.41/1.59  
% 3.41/1.59  %Foreground sorts:
% 3.41/1.59  
% 3.41/1.59  
% 3.41/1.59  %Background operators:
% 3.41/1.59  
% 3.41/1.59  
% 3.41/1.59  %Foreground operators:
% 3.41/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.41/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.41/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.59  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.41/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.41/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.41/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.41/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.41/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.60  
% 3.41/1.61  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.41/1.61  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.41/1.61  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.41/1.61  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.41/1.61  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.41/1.61  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.41/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.41/1.61  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.41/1.61  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.41/1.61  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.41/1.61  tff(c_36, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.61  tff(c_57, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.41/1.61  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.61  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.61  tff(c_294, plain, (![B_63, A_64]: (v2_tops_1(B_63, A_64) | k1_tops_1(A_64, B_63)!=k1_xboole_0 | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.41/1.61  tff(c_301, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_294])).
% 3.41/1.61  tff(c_305, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_301])).
% 3.41/1.61  tff(c_306, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_57, c_305])).
% 3.41/1.61  tff(c_232, plain, (![A_59, B_60]: (r1_tarski(k1_tops_1(A_59, B_60), B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.41/1.61  tff(c_237, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_232])).
% 3.41/1.61  tff(c_241, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_237])).
% 3.41/1.61  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.61  tff(c_434, plain, (![A_74, B_75]: (v3_pre_topc(k1_tops_1(A_74, B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.41/1.61  tff(c_439, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_434])).
% 3.41/1.61  tff(c_443, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_439])).
% 3.41/1.61  tff(c_58, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.41/1.61  tff(c_62, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_58])).
% 3.41/1.61  tff(c_148, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.41/1.61  tff(c_162, plain, (![A_54]: (r1_tarski(A_54, u1_struct_0('#skF_1')) | ~r1_tarski(A_54, '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_148])).
% 3.41/1.61  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.41/1.61  tff(c_54, plain, (![C_35]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_35 | ~v3_pre_topc(C_35, '#skF_1') | ~r1_tarski(C_35, '#skF_2') | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.61  tff(c_272, plain, (![C_62]: (k1_xboole_0=C_62 | ~v3_pre_topc(C_62, '#skF_1') | ~r1_tarski(C_62, '#skF_2') | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_57, c_54])).
% 3.41/1.61  tff(c_691, plain, (![A_87]: (k1_xboole_0=A_87 | ~v3_pre_topc(A_87, '#skF_1') | ~r1_tarski(A_87, '#skF_2') | ~r1_tarski(A_87, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_272])).
% 3.41/1.61  tff(c_735, plain, (![A_88]: (k1_xboole_0=A_88 | ~v3_pre_topc(A_88, '#skF_1') | ~r1_tarski(A_88, '#skF_2'))), inference(resolution, [status(thm)], [c_162, c_691])).
% 3.41/1.61  tff(c_738, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_443, c_735])).
% 3.41/1.61  tff(c_741, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_241, c_738])).
% 3.41/1.61  tff(c_743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_741])).
% 3.41/1.61  tff(c_744, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.41/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.61  tff(c_750, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=k1_xboole_0 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.61  tff(c_758, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_750])).
% 3.41/1.61  tff(c_807, plain, (![A_98, C_99, B_100]: (r1_tarski(k4_xboole_0(A_98, C_99), B_100) | ~r1_tarski(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.41/1.61  tff(c_824, plain, (![B_101, B_102]: (r1_tarski(k1_xboole_0, B_101) | ~r1_tarski(B_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_758, c_807])).
% 3.41/1.61  tff(c_853, plain, (![B_103]: (r1_tarski(k1_xboole_0, B_103))), inference(resolution, [status(thm)], [c_6, c_824])).
% 3.41/1.61  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.61  tff(c_857, plain, (![B_103]: (k4_xboole_0(k1_xboole_0, B_103)=k1_xboole_0)), inference(resolution, [status(thm)], [c_853, c_10])).
% 3.41/1.61  tff(c_745, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.41/1.61  tff(c_38, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.61  tff(c_749, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_745, c_38])).
% 3.41/1.61  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.61  tff(c_747, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_745, c_40])).
% 3.41/1.61  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.61  tff(c_771, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_745, c_42])).
% 3.41/1.61  tff(c_1135, plain, (![A_120, B_121]: (k1_tops_1(A_120, B_121)=k1_xboole_0 | ~v2_tops_1(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.41/1.61  tff(c_1145, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1135])).
% 3.41/1.61  tff(c_1152, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_745, c_1145])).
% 3.41/1.61  tff(c_1693, plain, (![B_144, A_145, C_146]: (r1_tarski(B_144, k1_tops_1(A_145, C_146)) | ~r1_tarski(B_144, C_146) | ~v3_pre_topc(B_144, A_145) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.41/1.61  tff(c_1700, plain, (![B_144]: (r1_tarski(B_144, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_144, '#skF_2') | ~v3_pre_topc(B_144, '#skF_1') | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1693])).
% 3.41/1.61  tff(c_1883, plain, (![B_152]: (r1_tarski(B_152, k1_xboole_0) | ~r1_tarski(B_152, '#skF_2') | ~v3_pre_topc(B_152, '#skF_1') | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1152, c_1700])).
% 3.41/1.61  tff(c_1890, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_771, c_1883])).
% 3.41/1.61  tff(c_1897, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_749, c_747, c_1890])).
% 3.41/1.61  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.61  tff(c_869, plain, (![B_104, A_105]: (B_104=A_105 | ~r1_tarski(B_104, A_105) | ~r1_tarski(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.61  tff(c_888, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_869])).
% 3.41/1.61  tff(c_1903, plain, (k1_xboole_0='#skF_3' | k4_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1897, c_888])).
% 3.41/1.61  tff(c_1922, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_857, c_1903])).
% 3.41/1.61  tff(c_1924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_744, c_1922])).
% 3.41/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.61  
% 3.41/1.61  Inference rules
% 3.41/1.61  ----------------------
% 3.41/1.61  #Ref     : 0
% 3.41/1.61  #Sup     : 420
% 3.41/1.61  #Fact    : 0
% 3.41/1.61  #Define  : 0
% 3.41/1.61  #Split   : 9
% 3.41/1.61  #Chain   : 0
% 3.41/1.61  #Close   : 0
% 3.41/1.61  
% 3.41/1.61  Ordering : KBO
% 3.41/1.61  
% 3.41/1.61  Simplification rules
% 3.41/1.61  ----------------------
% 3.41/1.61  #Subsume      : 77
% 3.41/1.61  #Demod        : 167
% 3.41/1.61  #Tautology    : 193
% 3.41/1.61  #SimpNegUnit  : 6
% 3.41/1.61  #BackRed      : 2
% 3.41/1.61  
% 3.41/1.61  #Partial instantiations: 0
% 3.41/1.61  #Strategies tried      : 1
% 3.41/1.61  
% 3.41/1.61  Timing (in seconds)
% 3.41/1.61  ----------------------
% 3.41/1.62  Preprocessing        : 0.34
% 3.41/1.62  Parsing              : 0.18
% 3.41/1.62  CNF conversion       : 0.02
% 3.41/1.62  Main loop            : 0.48
% 3.41/1.62  Inferencing          : 0.16
% 3.41/1.62  Reduction            : 0.15
% 3.41/1.62  Demodulation         : 0.11
% 3.41/1.62  BG Simplification    : 0.02
% 3.41/1.62  Subsumption          : 0.11
% 3.41/1.62  Abstraction          : 0.02
% 3.41/1.62  MUC search           : 0.00
% 3.41/1.62  Cooper               : 0.00
% 3.41/1.62  Total                : 0.87
% 3.41/1.62  Index Insertion      : 0.00
% 3.41/1.62  Index Deletion       : 0.00
% 3.41/1.62  Index Matching       : 0.00
% 3.41/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
