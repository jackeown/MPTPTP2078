%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1280+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:42 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 427 expanded)
%              Number of leaves         :   24 ( 166 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 (1041 expanded)
%              Number of equality atoms :   40 ( 286 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_20,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_114,plain,(
    ! [A_33,B_34] :
      ( k2_pre_topc(A_33,k1_tops_1(A_33,B_34)) = B_34
      | ~ v5_tops_1(B_34,A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_129,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_123])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tops_1(A_10,B_11),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_51,plain,(
    ! [A_29,B_30] :
      ( k2_pre_topc(A_29,k2_pre_topc(A_29,B_30)) = k2_pre_topc(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_214,plain,(
    ! [A_43,B_44] :
      ( k2_pre_topc(A_43,k2_pre_topc(A_43,k1_tops_1(A_43,B_44))) = k2_pre_topc(A_43,k1_tops_1(A_43,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_10,c_51])).

tff(c_223,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_214])).

tff(c_229,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_129,c_129,c_223])).

tff(c_329,plain,(
    ! [A_47,B_48] :
      ( k9_subset_1(u1_struct_0(A_47),k2_pre_topc(A_47,B_48),k2_pre_topc(A_47,k3_subset_1(u1_struct_0(A_47),B_48))) = k2_tops_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_341,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_329])).

tff(c_361,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_341])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_27,plain,(
    ! [A_21,B_22] :
      ( k3_subset_1(A_21,k3_subset_1(A_21,B_22)) = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_27])).

tff(c_145,plain,(
    ! [A_37,B_38] :
      ( k3_subset_1(u1_struct_0(A_37),k2_pre_topc(A_37,k3_subset_1(u1_struct_0(A_37),B_38))) = k1_tops_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_145])).

tff(c_174,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_170])).

tff(c_276,plain,
    ( k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_174])).

tff(c_277,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_280,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_277])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_280])).

tff(c_286,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k2_pre_topc(A_18,k2_pre_topc(A_18,B_19)) = k2_pre_topc(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_294,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_286,c_18])).

tff(c_308,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_294])).

tff(c_285,plain,(
    k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k3_subset_1(u1_struct_0(A_1),k2_pre_topc(A_1,k3_subset_1(u1_struct_0(A_1),B_3))) = k1_tops_1(A_1,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_751,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(u1_struct_0(A_57),k2_pre_topc(A_57,k1_tops_1(A_57,B_58))) = k1_tops_1(A_57,k2_pre_topc(A_57,k3_subset_1(u1_struct_0(A_57),B_58)))
      | ~ m1_subset_1(k2_pre_topc(A_57,k3_subset_1(u1_struct_0(A_57),B_58)),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_145])).

tff(c_774,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_751])).

tff(c_779,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_286,c_26,c_24,c_229,c_229,c_30,c_285,c_774])).

tff(c_43,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_pre_topc(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k3_subset_1(A_16,k3_subset_1(A_16,B_17)) = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [A_25,B_26] :
      ( k3_subset_1(u1_struct_0(A_25),k3_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_26))) = k2_pre_topc(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_43,c_16])).

tff(c_795,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_46])).

tff(c_822,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_286,c_795])).

tff(c_350,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_329])).

tff(c_363,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_350])).

tff(c_393,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_396,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_393])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_396])).

tff(c_401,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_837,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_401])).

tff(c_840,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_308,c_837])).

tff(c_842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_840])).

%------------------------------------------------------------------------------
