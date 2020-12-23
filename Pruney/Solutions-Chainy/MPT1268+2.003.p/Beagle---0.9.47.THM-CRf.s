%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:46 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 133 expanded)
%              Number of leaves         :   33 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 373 expanded)
%              Number of equality atoms :   25 (  57 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_114,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_86,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_86,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_537,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k1_tops_1(A_96,B_97),B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_548,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_537])).

tff(c_561,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_548])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_693,plain,(
    ! [A_101,B_102] :
      ( v3_pre_topc(k1_tops_1(A_101,B_102),A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_704,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_693])).

tff(c_717,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_704])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_569,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_561,c_12])).

tff(c_452,plain,(
    ! [A_89,B_90,C_91] :
      ( k9_subset_1(A_89,B_90,C_91) = k3_xboole_0(B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_463,plain,(
    ! [B_92] : k9_subset_1(u1_struct_0('#skF_1'),B_92,'#skF_2') = k3_xboole_0(B_92,'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_452])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k9_subset_1(A_15,B_16,C_17),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_469,plain,(
    ! [B_92] :
      ( m1_subset_1(k3_xboole_0(B_92,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_20])).

tff(c_475,plain,(
    ! [B_92] : m1_subset_1(k3_xboole_0(B_92,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_469])).

tff(c_659,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_475])).

tff(c_60,plain,(
    ! [C_45] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_45
      | ~ v3_pre_topc(C_45,'#skF_1')
      | ~ r1_tarski(C_45,'#skF_2')
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_422,plain,(
    ! [C_45] :
      ( k1_xboole_0 = C_45
      | ~ v3_pre_topc(C_45,'#skF_1')
      | ~ r1_tarski(C_45,'#skF_2')
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_60])).

tff(c_726,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_659,c_422])).

tff(c_736,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_717,c_726])).

tff(c_887,plain,(
    ! [B_111,A_112] :
      ( v2_tops_1(B_111,A_112)
      | k1_tops_1(A_112,B_111) != k1_xboole_0
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_903,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_887])).

tff(c_916,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_736,c_903])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_916])).

tff(c_919,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_920,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_924,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_44])).

tff(c_46,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_922,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_46])).

tff(c_48,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1024,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_48])).

tff(c_1506,plain,(
    ! [A_162,B_163] :
      ( k1_tops_1(A_162,B_163) = k1_xboole_0
      | ~ v2_tops_1(B_163,A_162)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1525,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1506])).

tff(c_1541,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_920,c_1525])).

tff(c_1896,plain,(
    ! [B_176,A_177,C_178] :
      ( r1_tarski(B_176,k1_tops_1(A_177,C_178))
      | ~ r1_tarski(B_176,C_178)
      | ~ v3_pre_topc(B_176,A_177)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1915,plain,(
    ! [B_176] :
      ( r1_tarski(B_176,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_176,'#skF_2')
      | ~ v3_pre_topc(B_176,'#skF_1')
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_1896])).

tff(c_1942,plain,(
    ! [B_179] :
      ( r1_tarski(B_179,k1_xboole_0)
      | ~ r1_tarski(B_179,'#skF_2')
      | ~ v3_pre_topc(B_179,'#skF_1')
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1541,c_1915])).

tff(c_1967,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1024,c_1942])).

tff(c_1982,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_924,c_922,c_1967])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1988,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1982,c_4])).

tff(c_1994,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1988])).

tff(c_1996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_919,c_1994])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:37:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.59  
% 3.48/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.59  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.59  
% 3.48/1.59  %Foreground sorts:
% 3.48/1.59  
% 3.48/1.59  
% 3.48/1.59  %Background operators:
% 3.48/1.59  
% 3.48/1.59  
% 3.48/1.59  %Foreground operators:
% 3.48/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.59  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.48/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.48/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.48/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.48/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.48/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.59  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.48/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.48/1.59  
% 3.48/1.60  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.48/1.60  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.48/1.60  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.48/1.60  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.48/1.60  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.48/1.60  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.48/1.60  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.48/1.60  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.48/1.60  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.48/1.60  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.48/1.60  tff(c_42, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.48/1.60  tff(c_86, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 3.48/1.60  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.48/1.60  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.48/1.60  tff(c_537, plain, (![A_96, B_97]: (r1_tarski(k1_tops_1(A_96, B_97), B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.48/1.60  tff(c_548, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_537])).
% 3.48/1.60  tff(c_561, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_548])).
% 3.48/1.60  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.48/1.60  tff(c_693, plain, (![A_101, B_102]: (v3_pre_topc(k1_tops_1(A_101, B_102), A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.48/1.60  tff(c_704, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_693])).
% 3.48/1.60  tff(c_717, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_704])).
% 3.48/1.60  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.60  tff(c_569, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_561, c_12])).
% 3.48/1.60  tff(c_452, plain, (![A_89, B_90, C_91]: (k9_subset_1(A_89, B_90, C_91)=k3_xboole_0(B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.48/1.60  tff(c_463, plain, (![B_92]: (k9_subset_1(u1_struct_0('#skF_1'), B_92, '#skF_2')=k3_xboole_0(B_92, '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_452])).
% 3.48/1.60  tff(c_20, plain, (![A_15, B_16, C_17]: (m1_subset_1(k9_subset_1(A_15, B_16, C_17), k1_zfmisc_1(A_15)) | ~m1_subset_1(C_17, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.48/1.60  tff(c_469, plain, (![B_92]: (m1_subset_1(k3_xboole_0(B_92, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_463, c_20])).
% 3.48/1.60  tff(c_475, plain, (![B_92]: (m1_subset_1(k3_xboole_0(B_92, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_469])).
% 3.48/1.60  tff(c_659, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_569, c_475])).
% 3.48/1.60  tff(c_60, plain, (![C_45]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_45 | ~v3_pre_topc(C_45, '#skF_1') | ~r1_tarski(C_45, '#skF_2') | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.48/1.60  tff(c_422, plain, (![C_45]: (k1_xboole_0=C_45 | ~v3_pre_topc(C_45, '#skF_1') | ~r1_tarski(C_45, '#skF_2') | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_86, c_60])).
% 3.48/1.60  tff(c_726, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_659, c_422])).
% 3.48/1.60  tff(c_736, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_561, c_717, c_726])).
% 3.48/1.60  tff(c_887, plain, (![B_111, A_112]: (v2_tops_1(B_111, A_112) | k1_tops_1(A_112, B_111)!=k1_xboole_0 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.48/1.60  tff(c_903, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_887])).
% 3.48/1.60  tff(c_916, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_736, c_903])).
% 3.48/1.60  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_916])).
% 3.48/1.60  tff(c_919, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 3.48/1.60  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.60  tff(c_920, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 3.48/1.60  tff(c_44, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.48/1.60  tff(c_924, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_920, c_44])).
% 3.48/1.60  tff(c_46, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.48/1.60  tff(c_922, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_920, c_46])).
% 3.48/1.60  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.48/1.60  tff(c_1024, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_48])).
% 3.48/1.60  tff(c_1506, plain, (![A_162, B_163]: (k1_tops_1(A_162, B_163)=k1_xboole_0 | ~v2_tops_1(B_163, A_162) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.48/1.60  tff(c_1525, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1506])).
% 3.48/1.60  tff(c_1541, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_920, c_1525])).
% 3.48/1.60  tff(c_1896, plain, (![B_176, A_177, C_178]: (r1_tarski(B_176, k1_tops_1(A_177, C_178)) | ~r1_tarski(B_176, C_178) | ~v3_pre_topc(B_176, A_177) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.48/1.60  tff(c_1915, plain, (![B_176]: (r1_tarski(B_176, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_176, '#skF_2') | ~v3_pre_topc(B_176, '#skF_1') | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_1896])).
% 3.48/1.60  tff(c_1942, plain, (![B_179]: (r1_tarski(B_179, k1_xboole_0) | ~r1_tarski(B_179, '#skF_2') | ~v3_pre_topc(B_179, '#skF_1') | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1541, c_1915])).
% 3.48/1.60  tff(c_1967, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1024, c_1942])).
% 3.48/1.60  tff(c_1982, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_924, c_922, c_1967])).
% 3.48/1.60  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.60  tff(c_1988, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1982, c_4])).
% 3.48/1.60  tff(c_1994, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1988])).
% 3.48/1.60  tff(c_1996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_919, c_1994])).
% 3.48/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  Inference rules
% 3.48/1.60  ----------------------
% 3.48/1.60  #Ref     : 2
% 3.48/1.60  #Sup     : 446
% 3.48/1.60  #Fact    : 0
% 3.48/1.60  #Define  : 0
% 3.48/1.60  #Split   : 5
% 3.48/1.60  #Chain   : 0
% 3.48/1.60  #Close   : 0
% 3.48/1.60  
% 3.48/1.60  Ordering : KBO
% 3.48/1.60  
% 3.48/1.60  Simplification rules
% 3.48/1.60  ----------------------
% 3.48/1.60  #Subsume      : 68
% 3.48/1.60  #Demod        : 226
% 3.48/1.60  #Tautology    : 229
% 3.48/1.60  #SimpNegUnit  : 4
% 3.48/1.60  #BackRed      : 11
% 3.48/1.60  
% 3.48/1.60  #Partial instantiations: 0
% 3.48/1.60  #Strategies tried      : 1
% 3.48/1.60  
% 3.48/1.60  Timing (in seconds)
% 3.48/1.60  ----------------------
% 3.48/1.61  Preprocessing        : 0.32
% 3.48/1.61  Parsing              : 0.17
% 3.48/1.61  CNF conversion       : 0.02
% 3.48/1.61  Main loop            : 0.51
% 3.48/1.61  Inferencing          : 0.17
% 3.48/1.61  Reduction            : 0.19
% 3.48/1.61  Demodulation         : 0.14
% 3.48/1.61  BG Simplification    : 0.02
% 3.48/1.61  Subsumption          : 0.08
% 3.48/1.61  Abstraction          : 0.02
% 3.48/1.61  MUC search           : 0.00
% 3.48/1.61  Cooper               : 0.00
% 3.48/1.61  Total                : 0.86
% 3.48/1.61  Index Insertion      : 0.00
% 3.48/1.61  Index Deletion       : 0.00
% 3.48/1.61  Index Matching       : 0.00
% 3.48/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
