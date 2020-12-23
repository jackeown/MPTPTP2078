%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:15 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 338 expanded)
%              Number of leaves         :   28 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  126 ( 765 expanded)
%              Number of equality atoms :   29 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_133,plain,(
    ! [A_45,B_46] :
      ( k2_pre_topc(A_45,k1_tops_1(A_45,B_46)) = B_46
      | ~ v5_tops_1(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_139,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_133])).

tff(c_144,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_139])).

tff(c_26,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_145,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_26])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k2_tops_1(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_37,B_38,C_39] :
      ( k4_subset_1(A_37,B_38,C_39) = k2_xboole_0(B_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [B_40] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_40,'#skF_2') = k2_xboole_0(B_40,'#skF_2')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_99,plain,(
    ! [B_24] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_24),'#skF_2') = k2_xboole_0(k2_tops_1('#skF_1',B_24),'#skF_2')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_95])).

tff(c_171,plain,(
    ! [B_49] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_49),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_99])).

tff(c_189,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_171])).

tff(c_223,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k3_subset_1(A_57,k4_subset_1(A_57,B_58,C_59)),k3_subset_1(A_57,B_58))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_232,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_223])).

tff(c_243,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_232])).

tff(c_337,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_340,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_337])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_340])).

tff(c_346,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k1_tops_1(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_103,plain,(
    ! [B_22] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_22),'#skF_2') = k2_xboole_0(k1_tops_1('#skF_1',B_22),'#skF_2')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_194,plain,(
    ! [B_50] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_50),'#skF_2') = k2_xboole_0('#skF_2',k1_tops_1('#skF_1',B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_103])).

tff(c_212,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_194])).

tff(c_229,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_223])).

tff(c_241,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_229])).

tff(c_255,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_258,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_255])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_258])).

tff(c_264,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_14,plain,(
    ! [A_16,B_17] :
      ( k2_pre_topc(A_16,k2_pre_topc(A_16,B_17)) = k2_pre_topc(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_276,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_264,c_14])).

tff(c_295,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_144,c_144,c_276])).

tff(c_155,plain,(
    ! [A_47,B_48] :
      ( k4_subset_1(u1_struct_0(A_47),B_48,k2_tops_1(A_47,B_48)) = k2_pre_topc(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_161,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_155])).

tff(c_166,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_161])).

tff(c_300,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_166])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( k4_subset_1(A_5,B_6,C_7) = k2_xboole_0(B_6,C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_755,plain,(
    ! [B_72] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_72,k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_72,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_346,c_6])).

tff(c_775,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_755])).

tff(c_787,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_775])).

tff(c_789,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_189])).

tff(c_8,plain,(
    ! [B_9,C_11,A_8] :
      ( r1_tarski(B_9,C_11)
      | ~ r1_tarski(k3_subset_1(A_8,C_11),k3_subset_1(A_8,B_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_239,plain,(
    ! [B_58,A_57,C_59] :
      ( r1_tarski(B_58,k4_subset_1(A_57,B_58,C_59))
      | ~ m1_subset_1(k4_subset_1(A_57,B_58,C_59),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_223,c_8])).

tff(c_823,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_239])).

tff(c_830,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_30,c_30,c_789,c_823])).

tff(c_832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_830])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.54  
% 3.23/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.54  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.23/1.54  
% 3.23/1.54  %Foreground sorts:
% 3.23/1.54  
% 3.23/1.54  
% 3.23/1.54  %Background operators:
% 3.23/1.54  
% 3.23/1.54  
% 3.23/1.54  %Foreground operators:
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.54  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.23/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.23/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.23/1.54  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.23/1.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.23/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.54  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.54  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.23/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.54  
% 3.23/1.56  tff(f_97, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 3.23/1.56  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 3.23/1.56  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.23/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.23/1.56  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.23/1.56  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 3.23/1.56  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.23/1.56  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 3.23/1.56  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.23/1.56  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.23/1.56  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.56  tff(c_28, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.56  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.56  tff(c_133, plain, (![A_45, B_46]: (k2_pre_topc(A_45, k1_tops_1(A_45, B_46))=B_46 | ~v5_tops_1(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.23/1.56  tff(c_139, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_133])).
% 3.23/1.56  tff(c_144, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_139])).
% 3.23/1.56  tff(c_26, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.23/1.56  tff(c_145, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_26])).
% 3.23/1.56  tff(c_22, plain, (![A_23, B_24]: (m1_subset_1(k2_tops_1(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.23/1.56  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.56  tff(c_85, plain, (![A_37, B_38, C_39]: (k4_subset_1(A_37, B_38, C_39)=k2_xboole_0(B_38, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.56  tff(c_95, plain, (![B_40]: (k4_subset_1(u1_struct_0('#skF_1'), B_40, '#skF_2')=k2_xboole_0(B_40, '#skF_2') | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_30, c_85])).
% 3.23/1.56  tff(c_99, plain, (![B_24]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_24), '#skF_2')=k2_xboole_0(k2_tops_1('#skF_1', B_24), '#skF_2') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_95])).
% 3.23/1.56  tff(c_171, plain, (![B_49]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_49), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_99])).
% 3.23/1.56  tff(c_189, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_171])).
% 3.23/1.56  tff(c_223, plain, (![A_57, B_58, C_59]: (r1_tarski(k3_subset_1(A_57, k4_subset_1(A_57, B_58, C_59)), k3_subset_1(A_57, B_58)) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.56  tff(c_232, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_189, c_223])).
% 3.23/1.56  tff(c_243, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_232])).
% 3.23/1.56  tff(c_337, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_243])).
% 3.23/1.56  tff(c_340, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_337])).
% 3.23/1.56  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_340])).
% 3.23/1.56  tff(c_346, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_243])).
% 3.23/1.56  tff(c_20, plain, (![A_21, B_22]: (m1_subset_1(k1_tops_1(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.23/1.56  tff(c_103, plain, (![B_22]: (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_22), '#skF_2')=k2_xboole_0(k1_tops_1('#skF_1', B_22), '#skF_2') | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_95])).
% 3.23/1.56  tff(c_194, plain, (![B_50]: (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_50), '#skF_2')=k2_xboole_0('#skF_2', k1_tops_1('#skF_1', B_50)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_103])).
% 3.23/1.56  tff(c_212, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_194])).
% 3.23/1.56  tff(c_229, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_212, c_223])).
% 3.23/1.56  tff(c_241, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_229])).
% 3.23/1.56  tff(c_255, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_241])).
% 3.23/1.56  tff(c_258, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_255])).
% 3.23/1.56  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_258])).
% 3.23/1.56  tff(c_264, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_241])).
% 3.23/1.56  tff(c_14, plain, (![A_16, B_17]: (k2_pre_topc(A_16, k2_pre_topc(A_16, B_17))=k2_pre_topc(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.56  tff(c_276, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_264, c_14])).
% 3.23/1.56  tff(c_295, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_144, c_144, c_276])).
% 3.23/1.56  tff(c_155, plain, (![A_47, B_48]: (k4_subset_1(u1_struct_0(A_47), B_48, k2_tops_1(A_47, B_48))=k2_pre_topc(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.23/1.56  tff(c_161, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_155])).
% 3.23/1.56  tff(c_166, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_161])).
% 3.23/1.56  tff(c_300, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_166])).
% 3.23/1.56  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_subset_1(A_5, B_6, C_7)=k2_xboole_0(B_6, C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.56  tff(c_755, plain, (![B_72]: (k4_subset_1(u1_struct_0('#skF_1'), B_72, k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_72, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_346, c_6])).
% 3.23/1.56  tff(c_775, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_755])).
% 3.23/1.56  tff(c_787, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_300, c_775])).
% 3.23/1.56  tff(c_789, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_787, c_189])).
% 3.23/1.56  tff(c_8, plain, (![B_9, C_11, A_8]: (r1_tarski(B_9, C_11) | ~r1_tarski(k3_subset_1(A_8, C_11), k3_subset_1(A_8, B_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.23/1.56  tff(c_239, plain, (![B_58, A_57, C_59]: (r1_tarski(B_58, k4_subset_1(A_57, B_58, C_59)) | ~m1_subset_1(k4_subset_1(A_57, B_58, C_59), k1_zfmisc_1(A_57)) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_223, c_8])).
% 3.23/1.56  tff(c_823, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_789, c_239])).
% 3.23/1.56  tff(c_830, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_30, c_30, c_789, c_823])).
% 3.23/1.56  tff(c_832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_830])).
% 3.23/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.56  
% 3.23/1.56  Inference rules
% 3.23/1.56  ----------------------
% 3.23/1.56  #Ref     : 0
% 3.23/1.56  #Sup     : 200
% 3.23/1.56  #Fact    : 0
% 3.23/1.56  #Define  : 0
% 3.23/1.56  #Split   : 7
% 3.23/1.56  #Chain   : 0
% 3.23/1.56  #Close   : 0
% 3.23/1.56  
% 3.23/1.56  Ordering : KBO
% 3.23/1.56  
% 3.23/1.56  Simplification rules
% 3.23/1.56  ----------------------
% 3.23/1.56  #Subsume      : 7
% 3.23/1.56  #Demod        : 148
% 3.23/1.56  #Tautology    : 79
% 3.23/1.56  #SimpNegUnit  : 1
% 3.23/1.56  #BackRed      : 4
% 3.23/1.56  
% 3.23/1.56  #Partial instantiations: 0
% 3.23/1.56  #Strategies tried      : 1
% 3.23/1.56  
% 3.23/1.56  Timing (in seconds)
% 3.23/1.56  ----------------------
% 3.34/1.56  Preprocessing        : 0.36
% 3.34/1.56  Parsing              : 0.19
% 3.34/1.56  CNF conversion       : 0.03
% 3.34/1.56  Main loop            : 0.39
% 3.34/1.56  Inferencing          : 0.12
% 3.34/1.56  Reduction            : 0.15
% 3.34/1.56  Demodulation         : 0.11
% 3.34/1.56  BG Simplification    : 0.02
% 3.34/1.56  Subsumption          : 0.07
% 3.34/1.56  Abstraction          : 0.02
% 3.34/1.56  MUC search           : 0.00
% 3.34/1.56  Cooper               : 0.00
% 3.34/1.56  Total                : 0.78
% 3.34/1.56  Index Insertion      : 0.00
% 3.34/1.56  Index Deletion       : 0.00
% 3.34/1.56  Index Matching       : 0.00
% 3.34/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
