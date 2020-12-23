%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:23 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 225 expanded)
%              Number of leaves         :   43 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 ( 620 expanded)
%              Number of equality atoms :   11 (  62 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_78,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_64,plain,(
    ! [A_34] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_34))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_89,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_6',u1_pre_topc(A_34))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_7] : m1_subset_1('#skF_6',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_12])).

tff(c_303,plain,(
    ! [B_92,A_93] :
      ( v3_pre_topc(B_92,A_93)
      | ~ r2_hidden(B_92,u1_pre_topc(A_93))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_314,plain,(
    ! [A_94] :
      ( v3_pre_topc('#skF_6',A_94)
      | ~ r2_hidden('#skF_6',u1_pre_topc(A_94))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_90,c_303])).

tff(c_327,plain,(
    ! [A_95] :
      ( v3_pre_topc('#skF_6',A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_89,c_314])).

tff(c_145,plain,(
    ! [D_66] :
      ( v3_pre_topc(D_66,'#skF_4')
      | ~ r2_hidden(D_66,'#skF_6')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_154,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_145])).

tff(c_156,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_276,plain,(
    ! [D_88] :
      ( r2_hidden(D_88,'#skF_6')
      | ~ r2_hidden('#skF_5',D_88)
      | ~ v4_pre_topc(D_88,'#skF_4')
      | ~ v3_pre_topc(D_88,'#skF_4')
      | ~ m1_subset_1(D_88,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_280,plain,
    ( r2_hidden('#skF_6','#skF_6')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_276])).

tff(c_287,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_280])).

tff(c_291,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_330,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_291])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_330])).

tff(c_336,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [A_2] : k4_xboole_0(A_2,'#skF_6') = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4])).

tff(c_167,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_170,plain,(
    ! [A_7] : k4_xboole_0(A_7,'#skF_6') = k3_subset_1(A_7,'#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_167])).

tff(c_175,plain,(
    ! [A_7] : k3_subset_1(A_7,'#skF_6') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_170])).

tff(c_504,plain,(
    ! [A_116,B_117] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_116),B_117),A_116)
      | ~ v3_pre_topc(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_508,plain,(
    ! [A_116] :
      ( v4_pre_topc(u1_struct_0(A_116),A_116)
      | ~ v3_pre_topc('#skF_6',A_116)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_504])).

tff(c_512,plain,(
    ! [A_119] :
      ( v4_pre_topc(u1_struct_0(A_119),A_119)
      | ~ v3_pre_topc('#skF_6',A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_508])).

tff(c_60,plain,(
    ! [A_32] :
      ( l1_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_15] :
      ( r2_hidden(u1_struct_0(A_15),u1_pre_topc(A_15))
      | ~ v2_pre_topc(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_353,plain,(
    ! [B_98,A_99] :
      ( v3_pre_topc(B_98,A_99)
      | ~ r2_hidden(B_98,u1_pre_topc(A_99))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_378,plain,(
    ! [A_102] :
      ( v3_pre_topc(u1_struct_0(A_102),A_102)
      | ~ r2_hidden(u1_struct_0(A_102),u1_pre_topc(A_102))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_92,c_353])).

tff(c_398,plain,(
    ! [A_105] :
      ( v3_pre_topc(u1_struct_0(A_105),A_105)
      | ~ v2_pre_topc(A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_54,c_378])).

tff(c_155,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ r2_hidden(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_145])).

tff(c_162,plain,(
    ~ r2_hidden(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_284,plain,
    ( r2_hidden(u1_struct_0('#skF_4'),'#skF_6')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | ~ v4_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_276])).

tff(c_290,plain,
    ( ~ r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | ~ v4_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_284])).

tff(c_337,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_401,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_398,c_337])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_401])).

tff(c_406,plain,
    ( ~ v4_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_413,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_427,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_14,c_413])).

tff(c_430,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_427])).

tff(c_62,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(u1_struct_0(A_33))
      | ~ l1_struct_0(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_433,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_430,c_62])).

tff(c_436,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_433])).

tff(c_439,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_436])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_439])).

tff(c_444,plain,(
    ~ v4_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_515,plain,
    ( ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_512,c_444])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_336,c_515])).

tff(c_521,plain,(
    r2_hidden(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_524,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_521,c_18])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.76/1.39  
% 2.76/1.39  %Foreground sorts:
% 2.76/1.39  
% 2.76/1.39  
% 2.76/1.39  %Background operators:
% 2.76/1.39  
% 2.76/1.39  
% 2.76/1.39  %Foreground operators:
% 2.76/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.76/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.76/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.76/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.76/1.39  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.76/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.76/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.76/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.76/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.39  
% 2.76/1.41  tff(f_145, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.76/1.41  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.41  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_pre_topc)).
% 2.76/1.41  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.76/1.41  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.76/1.41  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.76/1.41  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.76/1.41  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 2.76/1.41  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.76/1.41  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.76/1.41  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.76/1.41  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.76/1.41  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.76/1.41  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.76/1.41  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.76/1.41  tff(c_70, plain, (k1_xboole_0='#skF_6'), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.76/1.41  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.41  tff(c_94, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2])).
% 2.76/1.41  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.76/1.41  tff(c_78, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.76/1.41  tff(c_64, plain, (![A_34]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_34)) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.76/1.41  tff(c_89, plain, (![A_34]: (r2_hidden('#skF_6', u1_pre_topc(A_34)) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64])).
% 2.76/1.41  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.76/1.41  tff(c_90, plain, (![A_7]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_12])).
% 2.76/1.41  tff(c_303, plain, (![B_92, A_93]: (v3_pre_topc(B_92, A_93) | ~r2_hidden(B_92, u1_pre_topc(A_93)) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.76/1.41  tff(c_314, plain, (![A_94]: (v3_pre_topc('#skF_6', A_94) | ~r2_hidden('#skF_6', u1_pre_topc(A_94)) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_90, c_303])).
% 2.76/1.41  tff(c_327, plain, (![A_95]: (v3_pre_topc('#skF_6', A_95) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(resolution, [status(thm)], [c_89, c_314])).
% 2.76/1.41  tff(c_145, plain, (![D_66]: (v3_pre_topc(D_66, '#skF_4') | ~r2_hidden(D_66, '#skF_6') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.76/1.41  tff(c_154, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~r2_hidden('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_90, c_145])).
% 2.76/1.41  tff(c_156, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_154])).
% 2.76/1.41  tff(c_276, plain, (![D_88]: (r2_hidden(D_88, '#skF_6') | ~r2_hidden('#skF_5', D_88) | ~v4_pre_topc(D_88, '#skF_4') | ~v3_pre_topc(D_88, '#skF_4') | ~m1_subset_1(D_88, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.76/1.41  tff(c_280, plain, (r2_hidden('#skF_6', '#skF_6') | ~r2_hidden('#skF_5', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_90, c_276])).
% 2.76/1.41  tff(c_287, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_156, c_280])).
% 2.76/1.41  tff(c_291, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_287])).
% 2.76/1.41  tff(c_330, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_327, c_291])).
% 2.76/1.41  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_330])).
% 2.76/1.41  tff(c_336, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_287])).
% 2.76/1.41  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.41  tff(c_93, plain, (![A_2]: (k4_xboole_0(A_2, '#skF_6')=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4])).
% 2.76/1.41  tff(c_167, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.41  tff(c_170, plain, (![A_7]: (k4_xboole_0(A_7, '#skF_6')=k3_subset_1(A_7, '#skF_6'))), inference(resolution, [status(thm)], [c_90, c_167])).
% 2.76/1.41  tff(c_175, plain, (![A_7]: (k3_subset_1(A_7, '#skF_6')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_170])).
% 2.76/1.41  tff(c_504, plain, (![A_116, B_117]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_116), B_117), A_116) | ~v3_pre_topc(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.76/1.41  tff(c_508, plain, (![A_116]: (v4_pre_topc(u1_struct_0(A_116), A_116) | ~v3_pre_topc('#skF_6', A_116) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(superposition, [status(thm), theory('equality')], [c_175, c_504])).
% 2.76/1.41  tff(c_512, plain, (![A_119]: (v4_pre_topc(u1_struct_0(A_119), A_119) | ~v3_pre_topc('#skF_6', A_119) | ~l1_pre_topc(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_508])).
% 2.76/1.41  tff(c_60, plain, (![A_32]: (l1_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.76/1.41  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.76/1.41  tff(c_74, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.76/1.41  tff(c_14, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.41  tff(c_54, plain, (![A_15]: (r2_hidden(u1_struct_0(A_15), u1_pre_topc(A_15)) | ~v2_pre_topc(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.41  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.41  tff(c_10, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.41  tff(c_92, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.76/1.41  tff(c_353, plain, (![B_98, A_99]: (v3_pre_topc(B_98, A_99) | ~r2_hidden(B_98, u1_pre_topc(A_99)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.76/1.41  tff(c_378, plain, (![A_102]: (v3_pre_topc(u1_struct_0(A_102), A_102) | ~r2_hidden(u1_struct_0(A_102), u1_pre_topc(A_102)) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_92, c_353])).
% 2.76/1.41  tff(c_398, plain, (![A_105]: (v3_pre_topc(u1_struct_0(A_105), A_105) | ~v2_pre_topc(A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_54, c_378])).
% 2.76/1.41  tff(c_155, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~r2_hidden(u1_struct_0('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_92, c_145])).
% 2.76/1.41  tff(c_162, plain, (~r2_hidden(u1_struct_0('#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_155])).
% 2.76/1.41  tff(c_284, plain, (r2_hidden(u1_struct_0('#skF_4'), '#skF_6') | ~r2_hidden('#skF_5', u1_struct_0('#skF_4')) | ~v4_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_92, c_276])).
% 2.76/1.41  tff(c_290, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_4')) | ~v4_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_162, c_284])).
% 2.76/1.41  tff(c_337, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_290])).
% 2.76/1.41  tff(c_401, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_398, c_337])).
% 2.76/1.41  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_401])).
% 2.76/1.41  tff(c_406, plain, (~v4_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~r2_hidden('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_290])).
% 2.76/1.41  tff(c_413, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_406])).
% 2.76/1.41  tff(c_427, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_413])).
% 2.76/1.41  tff(c_430, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_427])).
% 2.76/1.41  tff(c_62, plain, (![A_33]: (~v1_xboole_0(u1_struct_0(A_33)) | ~l1_struct_0(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.41  tff(c_433, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_430, c_62])).
% 2.76/1.41  tff(c_436, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_433])).
% 2.76/1.41  tff(c_439, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_436])).
% 2.76/1.41  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_439])).
% 2.76/1.41  tff(c_444, plain, (~v4_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_406])).
% 2.76/1.41  tff(c_515, plain, (~v3_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_512, c_444])).
% 2.76/1.41  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_336, c_515])).
% 2.76/1.41  tff(c_521, plain, (r2_hidden(u1_struct_0('#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_155])).
% 2.76/1.41  tff(c_18, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.76/1.41  tff(c_524, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_521, c_18])).
% 2.76/1.41  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_524])).
% 2.76/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  Inference rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Ref     : 0
% 2.76/1.41  #Sup     : 80
% 2.76/1.41  #Fact    : 0
% 2.76/1.41  #Define  : 0
% 2.76/1.41  #Split   : 8
% 2.76/1.41  #Chain   : 0
% 2.76/1.41  #Close   : 0
% 2.76/1.41  
% 2.76/1.41  Ordering : KBO
% 2.76/1.41  
% 2.76/1.41  Simplification rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Subsume      : 9
% 2.76/1.41  #Demod        : 21
% 2.76/1.41  #Tautology    : 20
% 2.76/1.41  #SimpNegUnit  : 3
% 2.76/1.41  #BackRed      : 0
% 2.76/1.41  
% 2.76/1.41  #Partial instantiations: 0
% 2.76/1.41  #Strategies tried      : 1
% 2.76/1.41  
% 2.76/1.41  Timing (in seconds)
% 2.76/1.41  ----------------------
% 2.76/1.42  Preprocessing        : 0.35
% 2.76/1.42  Parsing              : 0.18
% 2.76/1.42  CNF conversion       : 0.03
% 2.76/1.42  Main loop            : 0.29
% 2.76/1.42  Inferencing          : 0.11
% 2.76/1.42  Reduction            : 0.09
% 2.76/1.42  Demodulation         : 0.06
% 2.76/1.42  BG Simplification    : 0.02
% 2.76/1.42  Subsumption          : 0.05
% 2.76/1.42  Abstraction          : 0.01
% 2.76/1.42  MUC search           : 0.00
% 2.76/1.42  Cooper               : 0.00
% 2.76/1.42  Total                : 0.68
% 2.76/1.42  Index Insertion      : 0.00
% 2.76/1.42  Index Deletion       : 0.00
% 2.76/1.42  Index Matching       : 0.00
% 2.76/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
