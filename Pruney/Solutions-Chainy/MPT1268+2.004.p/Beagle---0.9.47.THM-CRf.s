%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:46 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 144 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 391 expanded)
%              Number of equality atoms :   33 (  69 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_72,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1119,plain,(
    ! [B_86,A_87] :
      ( v2_tops_1(B_86,A_87)
      | k1_tops_1(A_87,B_86) != k1_xboole_0
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1138,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1119])).

tff(c_1154,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1138])).

tff(c_1155,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1154])).

tff(c_829,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_tops_1(A_78,B_79),B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_840,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_829])).

tff(c_853,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_840])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_857,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_853,c_2])).

tff(c_181,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [B_50] : k9_subset_1(u1_struct_0('#skF_1'),B_50,'#skF_2') = k3_xboole_0(B_50,'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_232,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k9_subset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_237,plain,(
    ! [B_50] :
      ( m1_subset_1(k3_xboole_0(B_50,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_232])).

tff(c_240,plain,(
    ! [B_50] : m1_subset_1(k3_xboole_0(B_50,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_237])).

tff(c_871,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_240])).

tff(c_48,plain,(
    ! [C_36] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_36
      | ~ v3_pre_topc(C_36,'#skF_1')
      | ~ r1_tarski(C_36,'#skF_2')
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_802,plain,(
    ! [C_36] :
      ( k1_xboole_0 = C_36
      | ~ v3_pre_topc(C_36,'#skF_1')
      | ~ r1_tarski(C_36,'#skF_2')
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48])).

tff(c_891,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_871,c_802])).

tff(c_899,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_891])).

tff(c_1156,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1155,c_899])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1201,plain,(
    ! [A_90,B_91] :
      ( v3_pre_topc(k1_tops_1(A_90,B_91),A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1214,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1201])).

tff(c_1230,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1214])).

tff(c_1232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1156,c_1230])).

tff(c_1233,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1234,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1236,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_32])).

tff(c_34,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1238,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_34])).

tff(c_36,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1411,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_36])).

tff(c_1734,plain,(
    ! [A_121,B_122] :
      ( k1_tops_1(A_121,B_122) = k1_xboole_0
      | ~ v2_tops_1(B_122,A_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1765,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1734])).

tff(c_1794,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1234,c_1765])).

tff(c_1914,plain,(
    ! [B_128,A_129,C_130] :
      ( r1_tarski(B_128,k1_tops_1(A_129,C_130))
      | ~ r1_tarski(B_128,C_130)
      | ~ v3_pre_topc(B_128,A_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1933,plain,(
    ! [B_128] :
      ( r1_tarski(B_128,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_128,'#skF_2')
      | ~ v3_pre_topc(B_128,'#skF_1')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1914])).

tff(c_1976,plain,(
    ! [B_132] :
      ( r1_tarski(B_132,k1_xboole_0)
      | ~ r1_tarski(B_132,'#skF_2')
      | ~ v3_pre_topc(B_132,'#skF_1')
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1794,c_1933])).

tff(c_2001,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1411,c_1976])).

tff(c_2018,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1236,c_1238,c_2001])).

tff(c_2023,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2018,c_2])).

tff(c_6,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1292,plain,(
    ! [A_97,B_98] : k1_setfam_1(k2_tarski(A_97,B_98)) = k3_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1307,plain,(
    ! [B_99,A_100] : k1_setfam_1(k2_tarski(B_99,A_100)) = k3_xboole_0(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1292])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1330,plain,(
    ! [B_101,A_102] : k3_xboole_0(B_101,A_102) = k3_xboole_0(A_102,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_12])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1272,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1280,plain,(
    ! [A_3] : k3_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_1272])).

tff(c_1346,plain,(
    ! [B_101] : k3_xboole_0(B_101,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1330,c_1280])).

tff(c_2030,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2023,c_1346])).

tff(c_2038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1233,c_2030])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.57  
% 3.50/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.57  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.50/1.57  
% 3.50/1.57  %Foreground sorts:
% 3.50/1.57  
% 3.50/1.57  
% 3.50/1.57  %Background operators:
% 3.50/1.57  
% 3.50/1.57  
% 3.50/1.57  %Foreground operators:
% 3.50/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.57  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.50/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.50/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.57  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.50/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.50/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.50/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.50/1.57  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.50/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.50/1.57  
% 3.50/1.58  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.50/1.58  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.50/1.58  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.50/1.58  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.50/1.58  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.50/1.58  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.50/1.58  tff(f_51, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.50/1.58  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.50/1.58  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.50/1.58  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.50/1.58  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.50/1.58  tff(c_30, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_50, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.50/1.58  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_1119, plain, (![B_86, A_87]: (v2_tops_1(B_86, A_87) | k1_tops_1(A_87, B_86)!=k1_xboole_0 | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.58  tff(c_1138, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1119])).
% 3.50/1.58  tff(c_1154, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1138])).
% 3.50/1.58  tff(c_1155, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_1154])).
% 3.50/1.58  tff(c_829, plain, (![A_78, B_79]: (r1_tarski(k1_tops_1(A_78, B_79), B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.58  tff(c_840, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_829])).
% 3.50/1.58  tff(c_853, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_840])).
% 3.50/1.58  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.50/1.58  tff(c_857, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_853, c_2])).
% 3.50/1.58  tff(c_181, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.50/1.58  tff(c_184, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_1'), B_50, '#skF_2')=k3_xboole_0(B_50, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_181])).
% 3.50/1.58  tff(c_232, plain, (![A_54, B_55, C_56]: (m1_subset_1(k9_subset_1(A_54, B_55, C_56), k1_zfmisc_1(A_54)) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.50/1.58  tff(c_237, plain, (![B_50]: (m1_subset_1(k3_xboole_0(B_50, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_184, c_232])).
% 3.50/1.58  tff(c_240, plain, (![B_50]: (m1_subset_1(k3_xboole_0(B_50, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_237])).
% 3.50/1.58  tff(c_871, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_857, c_240])).
% 3.50/1.58  tff(c_48, plain, (![C_36]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_36 | ~v3_pre_topc(C_36, '#skF_1') | ~r1_tarski(C_36, '#skF_2') | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_802, plain, (![C_36]: (k1_xboole_0=C_36 | ~v3_pre_topc(C_36, '#skF_1') | ~r1_tarski(C_36, '#skF_2') | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_48])).
% 3.50/1.58  tff(c_891, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_871, c_802])).
% 3.50/1.58  tff(c_899, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_853, c_891])).
% 3.50/1.58  tff(c_1156, plain, (~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1155, c_899])).
% 3.50/1.58  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_1201, plain, (![A_90, B_91]: (v3_pre_topc(k1_tops_1(A_90, B_91), A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.50/1.58  tff(c_1214, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1201])).
% 3.50/1.58  tff(c_1230, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1214])).
% 3.50/1.58  tff(c_1232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1156, c_1230])).
% 3.50/1.58  tff(c_1233, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.50/1.58  tff(c_1234, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.50/1.58  tff(c_32, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_1236, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_32])).
% 3.50/1.58  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_1238, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_34])).
% 3.50/1.58  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_1411, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_36])).
% 3.50/1.58  tff(c_1734, plain, (![A_121, B_122]: (k1_tops_1(A_121, B_122)=k1_xboole_0 | ~v2_tops_1(B_122, A_121) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.58  tff(c_1765, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1734])).
% 3.50/1.58  tff(c_1794, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1234, c_1765])).
% 3.50/1.58  tff(c_1914, plain, (![B_128, A_129, C_130]: (r1_tarski(B_128, k1_tops_1(A_129, C_130)) | ~r1_tarski(B_128, C_130) | ~v3_pre_topc(B_128, A_129) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.50/1.58  tff(c_1933, plain, (![B_128]: (r1_tarski(B_128, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_128, '#skF_2') | ~v3_pre_topc(B_128, '#skF_1') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1914])).
% 3.50/1.58  tff(c_1976, plain, (![B_132]: (r1_tarski(B_132, k1_xboole_0) | ~r1_tarski(B_132, '#skF_2') | ~v3_pre_topc(B_132, '#skF_1') | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1794, c_1933])).
% 3.50/1.58  tff(c_2001, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1411, c_1976])).
% 3.50/1.58  tff(c_2018, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1236, c_1238, c_2001])).
% 3.50/1.58  tff(c_2023, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_2018, c_2])).
% 3.50/1.58  tff(c_6, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.50/1.58  tff(c_1292, plain, (![A_97, B_98]: (k1_setfam_1(k2_tarski(A_97, B_98))=k3_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.50/1.58  tff(c_1307, plain, (![B_99, A_100]: (k1_setfam_1(k2_tarski(B_99, A_100))=k3_xboole_0(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1292])).
% 3.50/1.58  tff(c_12, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.50/1.58  tff(c_1330, plain, (![B_101, A_102]: (k3_xboole_0(B_101, A_102)=k3_xboole_0(A_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_1307, c_12])).
% 3.50/1.58  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.58  tff(c_1272, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.50/1.58  tff(c_1280, plain, (![A_3]: (k3_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1272])).
% 3.50/1.58  tff(c_1346, plain, (![B_101]: (k3_xboole_0(B_101, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1330, c_1280])).
% 3.50/1.58  tff(c_2030, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2023, c_1346])).
% 3.50/1.58  tff(c_2038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1233, c_2030])).
% 3.50/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.58  
% 3.50/1.58  Inference rules
% 3.50/1.58  ----------------------
% 3.50/1.58  #Ref     : 0
% 3.50/1.58  #Sup     : 438
% 3.50/1.58  #Fact    : 0
% 3.50/1.58  #Define  : 0
% 3.50/1.58  #Split   : 8
% 3.50/1.58  #Chain   : 0
% 3.50/1.58  #Close   : 0
% 3.50/1.58  
% 3.50/1.58  Ordering : KBO
% 3.50/1.58  
% 3.50/1.58  Simplification rules
% 3.50/1.58  ----------------------
% 3.50/1.58  #Subsume      : 15
% 3.50/1.58  #Demod        : 391
% 3.50/1.58  #Tautology    : 243
% 3.50/1.58  #SimpNegUnit  : 16
% 3.50/1.58  #BackRed      : 7
% 3.50/1.58  
% 3.50/1.58  #Partial instantiations: 0
% 3.50/1.58  #Strategies tried      : 1
% 3.50/1.59  
% 3.50/1.59  Timing (in seconds)
% 3.50/1.59  ----------------------
% 3.50/1.59  Preprocessing        : 0.31
% 3.50/1.59  Parsing              : 0.17
% 3.50/1.59  CNF conversion       : 0.02
% 3.50/1.59  Main loop            : 0.50
% 3.50/1.59  Inferencing          : 0.16
% 3.50/1.59  Reduction            : 0.21
% 3.50/1.59  Demodulation         : 0.16
% 3.50/1.59  BG Simplification    : 0.02
% 3.50/1.59  Subsumption          : 0.07
% 3.50/1.59  Abstraction          : 0.02
% 3.50/1.59  MUC search           : 0.00
% 3.50/1.59  Cooper               : 0.00
% 3.50/1.59  Total                : 0.85
% 3.50/1.59  Index Insertion      : 0.00
% 3.50/1.59  Index Deletion       : 0.00
% 3.50/1.59  Index Matching       : 0.00
% 3.50/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
