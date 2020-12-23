%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:00 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 284 expanded)
%              Number of leaves         :   25 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 730 expanded)
%              Number of equality atoms :    7 (  64 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_pre_topc(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(B_34,k2_pre_topc(A_35,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_50])).

tff(c_59,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_55])).

tff(c_69,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k2_pre_topc(A_38,B_39),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k3_subset_1(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_208,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(u1_struct_0(A_61),k2_pre_topc(A_61,B_62)) = k3_subset_1(u1_struct_0(A_61),k2_pre_topc(A_61,B_62))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_69,c_4])).

tff(c_215,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_208])).

tff(c_220,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_215])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k3_subset_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( r1_tarski(k4_xboole_0(C_3,B_2),k4_xboole_0(C_3,A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_135,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_tops_1(C_52,A_53)
      | ~ r1_tarski(B_54,C_52)
      | ~ v1_tops_1(B_54,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_321,plain,(
    ! [C_73,A_74,A_75,B_76] :
      ( v1_tops_1(k4_xboole_0(C_73,A_74),A_75)
      | ~ v1_tops_1(k4_xboole_0(C_73,B_76),A_75)
      | ~ m1_subset_1(k4_xboole_0(C_73,A_74),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(k4_xboole_0(C_73,B_76),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(resolution,[status(thm)],[c_2,c_135])).

tff(c_329,plain,(
    ! [A_75,B_76] :
      ( v1_tops_1(k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2'),A_75)
      | ~ v1_tops_1(k4_xboole_0(u1_struct_0('#skF_1'),B_76),A_75)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(k4_xboole_0(u1_struct_0('#skF_1'),B_76),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ r1_tarski('#skF_2',B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_321])).

tff(c_620,plain,(
    ! [A_99,B_100] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_99)
      | ~ v1_tops_1(k4_xboole_0(u1_struct_0('#skF_1'),B_100),A_99)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(k4_xboole_0(u1_struct_0('#skF_1'),B_100),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ r1_tarski('#skF_2',B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_329])).

tff(c_635,plain,(
    ! [A_99] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_99)
      | ~ v1_tops_1(k4_xboole_0(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),A_99)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_620])).

tff(c_906,plain,(
    ! [A_145] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_145)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),A_145)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_220,c_635])).

tff(c_910,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_906])).

tff(c_913,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_910])).

tff(c_914,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_913])).

tff(c_915,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_914])).

tff(c_918,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_915])).

tff(c_922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_918])).

tff(c_924,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_914])).

tff(c_24,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_103,plain,(
    ! [A_42,B_43] :
      ( v2_tops_1(k2_pre_topc(A_42,B_43),A_42)
      | ~ v3_tops_1(B_43,A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_110,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_103])).

tff(c_115,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_110])).

tff(c_14,plain,(
    ! [A_13,B_15] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_13),B_15),A_13)
      | ~ v2_tops_1(B_15,A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_923,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_914])).

tff(c_954,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_923])).

tff(c_957,plain,
    ( ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_954])).

tff(c_961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_924,c_115,c_957])).

tff(c_962,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_966,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_962])).

tff(c_970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:49:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.64  
% 3.89/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.65  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.89/1.65  
% 3.89/1.65  %Foreground sorts:
% 3.89/1.65  
% 3.89/1.65  
% 3.89/1.65  %Background operators:
% 3.89/1.65  
% 3.89/1.65  
% 3.89/1.65  %Foreground operators:
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.89/1.65  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.89/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.89/1.65  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.89/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.65  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.89/1.65  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.89/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.89/1.65  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.89/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.65  
% 3.89/1.66  tff(f_92, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 3.89/1.66  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.89/1.66  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.89/1.66  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.89/1.66  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.89/1.66  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 3.89/1.66  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 3.89/1.66  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 3.89/1.66  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 3.89/1.66  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.89/1.66  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.89/1.66  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.89/1.66  tff(c_8, plain, (![A_8, B_9]: (m1_subset_1(k2_pre_topc(A_8, B_9), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.66  tff(c_22, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.89/1.66  tff(c_50, plain, (![B_34, A_35]: (r1_tarski(B_34, k2_pre_topc(A_35, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.89/1.66  tff(c_55, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_50])).
% 3.89/1.66  tff(c_59, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_55])).
% 3.89/1.66  tff(c_69, plain, (![A_38, B_39]: (m1_subset_1(k2_pre_topc(A_38, B_39), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.66  tff(c_4, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k3_subset_1(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.89/1.66  tff(c_208, plain, (![A_61, B_62]: (k4_xboole_0(u1_struct_0(A_61), k2_pre_topc(A_61, B_62))=k3_subset_1(u1_struct_0(A_61), k2_pre_topc(A_61, B_62)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_69, c_4])).
% 3.89/1.66  tff(c_215, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_208])).
% 3.89/1.66  tff(c_220, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_215])).
% 3.89/1.66  tff(c_30, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k3_subset_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.89/1.66  tff(c_38, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_26, c_30])).
% 3.89/1.66  tff(c_2, plain, (![C_3, B_2, A_1]: (r1_tarski(k4_xboole_0(C_3, B_2), k4_xboole_0(C_3, A_1)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.89/1.66  tff(c_135, plain, (![C_52, A_53, B_54]: (v1_tops_1(C_52, A_53) | ~r1_tarski(B_54, C_52) | ~v1_tops_1(B_54, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.89/1.66  tff(c_321, plain, (![C_73, A_74, A_75, B_76]: (v1_tops_1(k4_xboole_0(C_73, A_74), A_75) | ~v1_tops_1(k4_xboole_0(C_73, B_76), A_75) | ~m1_subset_1(k4_xboole_0(C_73, A_74), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(k4_xboole_0(C_73, B_76), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~r1_tarski(A_74, B_76))), inference(resolution, [status(thm)], [c_2, c_135])).
% 3.89/1.66  tff(c_329, plain, (![A_75, B_76]: (v1_tops_1(k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2'), A_75) | ~v1_tops_1(k4_xboole_0(u1_struct_0('#skF_1'), B_76), A_75) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(k4_xboole_0(u1_struct_0('#skF_1'), B_76), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~r1_tarski('#skF_2', B_76))), inference(superposition, [status(thm), theory('equality')], [c_38, c_321])).
% 3.89/1.66  tff(c_620, plain, (![A_99, B_100]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_99) | ~v1_tops_1(k4_xboole_0(u1_struct_0('#skF_1'), B_100), A_99) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(k4_xboole_0(u1_struct_0('#skF_1'), B_100), k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~r1_tarski('#skF_2', B_100))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_329])).
% 3.89/1.66  tff(c_635, plain, (![A_99]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_99) | ~v1_tops_1(k4_xboole_0(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), A_99) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_220, c_620])).
% 3.89/1.66  tff(c_906, plain, (![A_145]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_145) | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), A_145) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_220, c_635])).
% 3.89/1.66  tff(c_910, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_906])).
% 3.89/1.66  tff(c_913, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_910])).
% 3.89/1.66  tff(c_914, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_22, c_913])).
% 3.89/1.66  tff(c_915, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_914])).
% 3.89/1.66  tff(c_918, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_915])).
% 3.89/1.66  tff(c_922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_918])).
% 3.89/1.66  tff(c_924, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_914])).
% 3.89/1.66  tff(c_24, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.89/1.66  tff(c_103, plain, (![A_42, B_43]: (v2_tops_1(k2_pre_topc(A_42, B_43), A_42) | ~v3_tops_1(B_43, A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.89/1.66  tff(c_110, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_103])).
% 3.89/1.66  tff(c_115, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_110])).
% 3.89/1.66  tff(c_14, plain, (![A_13, B_15]: (v1_tops_1(k3_subset_1(u1_struct_0(A_13), B_15), A_13) | ~v2_tops_1(B_15, A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.89/1.66  tff(c_923, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_914])).
% 3.89/1.66  tff(c_954, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_923])).
% 3.89/1.66  tff(c_957, plain, (~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_954])).
% 3.89/1.66  tff(c_961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_924, c_115, c_957])).
% 3.89/1.66  tff(c_962, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_923])).
% 3.89/1.66  tff(c_966, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_962])).
% 3.89/1.66  tff(c_970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_966])).
% 3.89/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.66  
% 3.89/1.66  Inference rules
% 3.89/1.66  ----------------------
% 3.89/1.66  #Ref     : 0
% 3.89/1.66  #Sup     : 224
% 3.89/1.66  #Fact    : 0
% 3.89/1.66  #Define  : 0
% 3.89/1.66  #Split   : 12
% 3.89/1.66  #Chain   : 0
% 3.89/1.66  #Close   : 0
% 3.89/1.66  
% 3.89/1.66  Ordering : KBO
% 3.89/1.66  
% 3.89/1.66  Simplification rules
% 3.89/1.66  ----------------------
% 3.89/1.66  #Subsume      : 34
% 3.89/1.66  #Demod        : 79
% 3.89/1.66  #Tautology    : 20
% 3.89/1.66  #SimpNegUnit  : 1
% 3.89/1.66  #BackRed      : 0
% 3.89/1.66  
% 3.89/1.66  #Partial instantiations: 0
% 3.89/1.66  #Strategies tried      : 1
% 3.89/1.66  
% 3.89/1.66  Timing (in seconds)
% 3.89/1.66  ----------------------
% 3.89/1.66  Preprocessing        : 0.32
% 3.89/1.66  Parsing              : 0.17
% 3.89/1.66  CNF conversion       : 0.02
% 3.89/1.66  Main loop            : 0.58
% 3.89/1.66  Inferencing          : 0.21
% 3.89/1.66  Reduction            : 0.17
% 3.89/1.66  Demodulation         : 0.11
% 3.89/1.66  BG Simplification    : 0.03
% 3.89/1.66  Subsumption          : 0.13
% 3.89/1.67  Abstraction          : 0.03
% 3.89/1.67  MUC search           : 0.00
% 3.89/1.67  Cooper               : 0.00
% 3.89/1.67  Total                : 0.93
% 3.89/1.67  Index Insertion      : 0.00
% 3.89/1.67  Index Deletion       : 0.00
% 3.89/1.67  Index Matching       : 0.00
% 3.89/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
