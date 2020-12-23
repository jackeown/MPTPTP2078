%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:47 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 179 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 509 expanded)
%              Number of equality atoms :   29 (  80 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_108,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_80,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_73,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_477,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k1_tops_1(A_81,B_82),B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_486,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_477])).

tff(c_496,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_486])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_503,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_496,c_12])).

tff(c_399,plain,(
    ! [A_70,B_71,C_72] :
      ( k9_subset_1(A_70,B_71,C_72) = k3_xboole_0(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_402,plain,(
    ! [B_71] : k9_subset_1(u1_struct_0('#skF_1'),B_71,'#skF_2') = k3_xboole_0(B_71,'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_399])).

tff(c_437,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1(k9_subset_1(A_77,B_78,C_79),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_446,plain,(
    ! [B_71] :
      ( m1_subset_1(k3_xboole_0(B_71,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_437])).

tff(c_450,plain,(
    ! [B_71] : m1_subset_1(k3_xboole_0(B_71,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_446])).

tff(c_526,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_450])).

tff(c_56,plain,(
    ! [C_40] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_40
      | ~ v3_pre_topc(C_40,'#skF_1')
      | ~ r1_tarski(C_40,'#skF_2')
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_428,plain,(
    ! [C_40] :
      ( k1_xboole_0 = C_40
      | ~ v3_pre_topc(C_40,'#skF_1')
      | ~ r1_tarski(C_40,'#skF_2')
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_56])).

tff(c_534,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_526,c_428])).

tff(c_542,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_534])).

tff(c_663,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_542])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_768,plain,(
    ! [A_93,B_94] :
      ( v3_pre_topc(k1_tops_1(A_93,B_94),A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_781,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_768])).

tff(c_797,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_781])).

tff(c_799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_663,c_797])).

tff(c_800,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_1096,plain,(
    ! [B_115,A_116] :
      ( v2_tops_1(B_115,A_116)
      | k1_tops_1(A_116,B_115) != k1_xboole_0
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1118,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1096])).

tff(c_1137,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_800,c_1118])).

tff(c_1139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1137])).

tff(c_1140,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1141,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1143,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_40])).

tff(c_42,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1241,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_42])).

tff(c_44,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1262,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_44])).

tff(c_1784,plain,(
    ! [A_162,B_163] :
      ( k1_tops_1(A_162,B_163) = k1_xboole_0
      | ~ v2_tops_1(B_163,A_162)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1809,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1784])).

tff(c_1832,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1141,c_1809])).

tff(c_1909,plain,(
    ! [B_167,A_168,C_169] :
      ( r1_tarski(B_167,k1_tops_1(A_168,C_169))
      | ~ r1_tarski(B_167,C_169)
      | ~ v3_pre_topc(B_167,A_168)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1926,plain,(
    ! [B_167] :
      ( r1_tarski(B_167,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_167,'#skF_2')
      | ~ v3_pre_topc(B_167,'#skF_1')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_1909])).

tff(c_2028,plain,(
    ! [B_172] :
      ( r1_tarski(B_172,k1_xboole_0)
      | ~ r1_tarski(B_172,'#skF_2')
      | ~ v3_pre_topc(B_172,'#skF_1')
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1832,c_1926])).

tff(c_2050,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1262,c_2028])).

tff(c_2066,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1241,c_2050])).

tff(c_1144,plain,(
    ! [B_117,A_118] : k2_xboole_0(B_117,A_118) = k2_xboole_0(A_118,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1197,plain,(
    ! [A_119] : k2_xboole_0(k1_xboole_0,A_119) = A_119 ),
    inference(superposition,[status(thm),theory(equality)],[c_1144,c_10])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1209,plain,(
    ! [A_119] : r1_tarski(k1_xboole_0,A_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_1197,c_14])).

tff(c_1403,plain,(
    ! [B_133,A_134] :
      ( B_133 = A_134
      | ~ r1_tarski(B_133,A_134)
      | ~ r1_tarski(A_134,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1416,plain,(
    ! [A_119] :
      ( k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1209,c_1403])).

tff(c_2072,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2066,c_1416])).

tff(c_2081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1140,c_2072])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:40:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.63  
% 3.60/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.63  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.60/1.63  
% 3.60/1.63  %Foreground sorts:
% 3.60/1.63  
% 3.60/1.63  
% 3.60/1.63  %Background operators:
% 3.60/1.63  
% 3.60/1.63  
% 3.60/1.63  %Foreground operators:
% 3.60/1.63  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.63  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.60/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.60/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.60/1.63  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.60/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.60/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.60/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.60/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.60/1.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.60/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.60/1.63  
% 3.92/1.65  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.92/1.65  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.92/1.65  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.92/1.65  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.92/1.65  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.92/1.65  tff(f_59, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.92/1.65  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.92/1.65  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.92/1.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.92/1.65  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.92/1.65  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.92/1.65  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.92/1.65  tff(c_38, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.92/1.65  tff(c_73, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 3.92/1.65  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.92/1.65  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.92/1.65  tff(c_477, plain, (![A_81, B_82]: (r1_tarski(k1_tops_1(A_81, B_82), B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.92/1.65  tff(c_486, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_477])).
% 3.92/1.65  tff(c_496, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_486])).
% 3.92/1.65  tff(c_12, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.92/1.65  tff(c_503, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_496, c_12])).
% 3.92/1.65  tff(c_399, plain, (![A_70, B_71, C_72]: (k9_subset_1(A_70, B_71, C_72)=k3_xboole_0(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.92/1.65  tff(c_402, plain, (![B_71]: (k9_subset_1(u1_struct_0('#skF_1'), B_71, '#skF_2')=k3_xboole_0(B_71, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_399])).
% 3.92/1.65  tff(c_437, plain, (![A_77, B_78, C_79]: (m1_subset_1(k9_subset_1(A_77, B_78, C_79), k1_zfmisc_1(A_77)) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.92/1.65  tff(c_446, plain, (![B_71]: (m1_subset_1(k3_xboole_0(B_71, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_402, c_437])).
% 3.92/1.65  tff(c_450, plain, (![B_71]: (m1_subset_1(k3_xboole_0(B_71, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_446])).
% 3.92/1.65  tff(c_526, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_503, c_450])).
% 3.92/1.65  tff(c_56, plain, (![C_40]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_40 | ~v3_pre_topc(C_40, '#skF_1') | ~r1_tarski(C_40, '#skF_2') | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.92/1.65  tff(c_428, plain, (![C_40]: (k1_xboole_0=C_40 | ~v3_pre_topc(C_40, '#skF_1') | ~r1_tarski(C_40, '#skF_2') | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_73, c_56])).
% 3.92/1.65  tff(c_534, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_526, c_428])).
% 3.92/1.65  tff(c_542, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_496, c_534])).
% 3.92/1.65  tff(c_663, plain, (~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_542])).
% 3.92/1.65  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.92/1.65  tff(c_768, plain, (![A_93, B_94]: (v3_pre_topc(k1_tops_1(A_93, B_94), A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.92/1.65  tff(c_781, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_768])).
% 3.92/1.65  tff(c_797, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_781])).
% 3.92/1.65  tff(c_799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_663, c_797])).
% 3.92/1.65  tff(c_800, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_542])).
% 3.92/1.65  tff(c_1096, plain, (![B_115, A_116]: (v2_tops_1(B_115, A_116) | k1_tops_1(A_116, B_115)!=k1_xboole_0 | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.92/1.65  tff(c_1118, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1096])).
% 3.92/1.65  tff(c_1137, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_800, c_1118])).
% 3.92/1.65  tff(c_1139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_1137])).
% 3.92/1.65  tff(c_1140, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 3.92/1.65  tff(c_1141, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 3.92/1.65  tff(c_40, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.92/1.65  tff(c_1143, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_40])).
% 3.92/1.65  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.92/1.65  tff(c_1241, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_42])).
% 3.92/1.65  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.92/1.65  tff(c_1262, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_44])).
% 3.92/1.65  tff(c_1784, plain, (![A_162, B_163]: (k1_tops_1(A_162, B_163)=k1_xboole_0 | ~v2_tops_1(B_163, A_162) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.92/1.65  tff(c_1809, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1784])).
% 3.92/1.65  tff(c_1832, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1141, c_1809])).
% 3.92/1.65  tff(c_1909, plain, (![B_167, A_168, C_169]: (r1_tarski(B_167, k1_tops_1(A_168, C_169)) | ~r1_tarski(B_167, C_169) | ~v3_pre_topc(B_167, A_168) | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.92/1.65  tff(c_1926, plain, (![B_167]: (r1_tarski(B_167, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_167, '#skF_2') | ~v3_pre_topc(B_167, '#skF_1') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_1909])).
% 3.92/1.65  tff(c_2028, plain, (![B_172]: (r1_tarski(B_172, k1_xboole_0) | ~r1_tarski(B_172, '#skF_2') | ~v3_pre_topc(B_172, '#skF_1') | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1832, c_1926])).
% 3.92/1.65  tff(c_2050, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1262, c_2028])).
% 3.92/1.65  tff(c_2066, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1241, c_2050])).
% 3.92/1.65  tff(c_1144, plain, (![B_117, A_118]: (k2_xboole_0(B_117, A_118)=k2_xboole_0(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.92/1.65  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.92/1.65  tff(c_1197, plain, (![A_119]: (k2_xboole_0(k1_xboole_0, A_119)=A_119)), inference(superposition, [status(thm), theory('equality')], [c_1144, c_10])).
% 3.92/1.65  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.92/1.65  tff(c_1209, plain, (![A_119]: (r1_tarski(k1_xboole_0, A_119))), inference(superposition, [status(thm), theory('equality')], [c_1197, c_14])).
% 3.92/1.65  tff(c_1403, plain, (![B_133, A_134]: (B_133=A_134 | ~r1_tarski(B_133, A_134) | ~r1_tarski(A_134, B_133))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.92/1.65  tff(c_1416, plain, (![A_119]: (k1_xboole_0=A_119 | ~r1_tarski(A_119, k1_xboole_0))), inference(resolution, [status(thm)], [c_1209, c_1403])).
% 3.92/1.65  tff(c_2072, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2066, c_1416])).
% 3.92/1.65  tff(c_2081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1140, c_2072])).
% 3.92/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.65  
% 3.92/1.65  Inference rules
% 3.92/1.65  ----------------------
% 3.92/1.65  #Ref     : 0
% 3.92/1.65  #Sup     : 434
% 3.92/1.65  #Fact    : 0
% 3.92/1.65  #Define  : 0
% 3.92/1.65  #Split   : 9
% 3.92/1.65  #Chain   : 0
% 3.92/1.65  #Close   : 0
% 3.92/1.65  
% 3.92/1.65  Ordering : KBO
% 3.92/1.65  
% 3.92/1.65  Simplification rules
% 3.92/1.65  ----------------------
% 3.92/1.65  #Subsume      : 34
% 3.92/1.65  #Demod        : 397
% 3.92/1.65  #Tautology    : 251
% 3.92/1.65  #SimpNegUnit  : 8
% 3.92/1.65  #BackRed      : 12
% 3.92/1.65  
% 3.92/1.65  #Partial instantiations: 0
% 3.92/1.65  #Strategies tried      : 1
% 3.92/1.65  
% 3.92/1.65  Timing (in seconds)
% 3.92/1.65  ----------------------
% 3.92/1.65  Preprocessing        : 0.34
% 3.92/1.65  Parsing              : 0.18
% 3.92/1.65  CNF conversion       : 0.02
% 3.92/1.65  Main loop            : 0.55
% 3.92/1.65  Inferencing          : 0.18
% 3.92/1.65  Reduction            : 0.21
% 3.92/1.65  Demodulation         : 0.16
% 3.92/1.65  BG Simplification    : 0.03
% 3.92/1.65  Subsumption          : 0.09
% 3.92/1.65  Abstraction          : 0.03
% 3.92/1.65  MUC search           : 0.00
% 3.92/1.65  Cooper               : 0.00
% 3.92/1.65  Total                : 0.93
% 3.92/1.65  Index Insertion      : 0.00
% 3.92/1.65  Index Deletion       : 0.00
% 3.92/1.66  Index Matching       : 0.00
% 3.92/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
