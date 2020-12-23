%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:28 EST 2020

% Result     : Theorem 9.59s
% Output     : CNFRefutation 9.95s
% Verified   : 
% Statistics : Number of formulae       :  285 (8370 expanded)
%              Number of leaves         :   24 (2817 expanded)
%              Depth                    :   22
%              Number of atoms          :  645 (23187 expanded)
%              Number of equality atoms :   72 (2541 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => ( v4_tops_1(k1_tops_1(A,B),A)
                & v4_tops_1(k2_pre_topc(A,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k1_tops_1(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_48,B_49] :
      ( k2_pre_topc(A_48,k2_pre_topc(A_48,B_49)) = k2_pre_topc(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_113,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108])).

tff(c_67,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k2_pre_topc(A_42,B_43),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(k1_tops_1(A_24,B_26),B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_137,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tops_1(A_52,k2_pre_topc(A_52,B_53)),k2_pre_topc(A_52,B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_67,c_26])).

tff(c_142,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_137])).

tff(c_148,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_113,c_142])).

tff(c_228,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_231,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_228])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_231])).

tff(c_237,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_81,plain,(
    ! [A_46,B_47] :
      ( k1_tops_1(A_46,k1_tops_1(A_46,B_47)) = k1_tops_1(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_87,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_92,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_87])).

tff(c_74,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k1_tops_1(A_44,B_45),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( r1_tarski(B_9,k2_pre_topc(A_7,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tops_1(A_50,B_51),k2_pre_topc(A_50,k1_tops_1(A_50,B_51)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_74,c_12])).

tff(c_131,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_123])).

tff(c_136,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_92,c_131])).

tff(c_198,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_201,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_201])).

tff(c_207,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_47,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tops_1(A_38,B_39),B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_49,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_52,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_49])).

tff(c_14,plain,(
    ! [A_10,B_14,C_16] :
      ( r1_tarski(k2_pre_topc(A_10,B_14),k2_pre_topc(A_10,C_16))
      | ~ r1_tarski(B_14,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_18,plain,(
    ! [B_19,A_17] :
      ( r1_tarski(B_19,k2_pre_topc(A_17,k1_tops_1(A_17,B_19)))
      | ~ v4_tops_1(B_19,A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_pre_topc(A_5,k2_pre_topc(A_5,B_6)) = k2_pre_topc(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_209,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_207,c_10])).

tff(c_218,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_209])).

tff(c_73,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tops_1(A_42,k2_pre_topc(A_42,B_43)),k2_pre_topc(A_42,B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_67,c_26])).

tff(c_290,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_73])).

tff(c_308,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_218,c_290])).

tff(c_771,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_774,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_771])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_207,c_774])).

tff(c_780,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_359,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(k2_pre_topc(A_62,B_63),k2_pre_topc(A_62,C_64))
      | ~ r1_tarski(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_373,plain,(
    ! [B_63] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_63),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_63,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_359])).

tff(c_395,plain,(
    ! [B_66] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_66),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_66,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_237,c_373])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_429,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_1',B_69) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',B_69))
      | ~ r1_tarski(B_69,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_395,c_2])).

tff(c_440,plain,(
    ! [C_16] :
      ( k2_pre_topc('#skF_1',C_16) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(C_16,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_429])).

tff(c_466,plain,(
    ! [C_16] :
      ( k2_pre_topc('#skF_1',C_16) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(C_16,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_440])).

tff(c_786,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_780,c_466])).

tff(c_806,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_786])).

tff(c_6201,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_806])).

tff(c_6257,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_6201])).

tff(c_6261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_6257])).

tff(c_6262,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_806])).

tff(c_6278,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6262])).

tff(c_6287,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_6278])).

tff(c_6297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_207,c_34,c_52,c_6287])).

tff(c_6298,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_6262])).

tff(c_206,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_6311,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6298,c_206])).

tff(c_644,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(k1_tops_1(A_76,B_77),k1_tops_1(A_76,C_78))
      | ~ r1_tarski(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_661,plain,(
    ! [C_78] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_78))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_644])).

tff(c_675,plain,(
    ! [C_78] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_78))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_207,c_661])).

tff(c_20,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k1_tops_1(A_17,k2_pre_topc(A_17,B_19)),B_19)
      | ~ v4_tops_1(B_19,A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k1_tops_1(A_22,k1_tops_1(A_22,B_23)) = k1_tops_1(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_241,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_237,c_24])).

tff(c_251,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_241])).

tff(c_236,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_835,plain,(
    ! [B_83,A_84] :
      ( v4_tops_1(B_83,A_84)
      | ~ r1_tarski(B_83,k2_pre_topc(A_84,k1_tops_1(A_84,B_83)))
      | ~ r1_tarski(k1_tops_1(A_84,k2_pre_topc(A_84,B_83)),B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_855,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_835])).

tff(c_867,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_237,c_236,c_855])).

tff(c_868,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_867])).

tff(c_3370,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_806])).

tff(c_3373,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_3370])).

tff(c_3377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_3373])).

tff(c_3378,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_806])).

tff(c_3440,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3378])).

tff(c_3446,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_3440])).

tff(c_3453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_207,c_34,c_52,c_3446])).

tff(c_3454,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_3378])).

tff(c_779,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_849,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_835])).

tff(c_864,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_780,c_779,c_849])).

tff(c_1370,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))) ),
    inference(splitLeft,[status(thm)],[c_864])).

tff(c_1417,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_1370])).

tff(c_1423,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_207,c_1417])).

tff(c_1547,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1423])).

tff(c_1550,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1547])).

tff(c_1554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_780,c_1550])).

tff(c_1555,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1423])).

tff(c_1628,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_675,c_1555])).

tff(c_1635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_206,c_1628])).

tff(c_1637,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))) ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_3457,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_3454,c_1637])).

tff(c_3469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_868,c_3457])).

tff(c_3470,plain,(
    v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_867])).

tff(c_382,plain,(
    ! [B_63] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_63),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_63,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_237,c_373])).

tff(c_189,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,k2_pre_topc(A_59,k1_tops_1(A_59,B_58)))
      | ~ v4_tops_1(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3481,plain,(
    ! [A_137,B_138] :
      ( k2_pre_topc(A_137,k1_tops_1(A_137,B_138)) = B_138
      | ~ r1_tarski(k2_pre_topc(A_137,k1_tops_1(A_137,B_138)),B_138)
      | ~ v4_tops_1(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_3488,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_382,c_3481])).

tff(c_3503,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_36,c_237,c_3470,c_3488])).

tff(c_3509,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3503])).

tff(c_3512,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_3509])).

tff(c_3516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_237,c_3512])).

tff(c_3518,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3503])).

tff(c_28,plain,(
    ! [A_27,B_31,C_33] :
      ( r1_tarski(k1_tops_1(A_27,B_31),k1_tops_1(A_27,C_33))
      | ~ r1_tarski(B_31,C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_678,plain,(
    ! [C_79] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_79))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_207,c_661])).

tff(c_4507,plain,(
    ! [C_159] :
      ( k1_tops_1('#skF_1',C_159) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1',C_159),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_678,c_2])).

tff(c_4518,plain,(
    ! [B_31] :
      ( k1_tops_1('#skF_1',B_31) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_31)
      | ~ r1_tarski(B_31,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_4507])).

tff(c_4572,plain,(
    ! [B_160] :
      ( k1_tops_1('#skF_1',B_160) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_160)
      | ~ r1_tarski(B_160,'#skF_2')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4518])).

tff(c_4575,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_3518,c_4572])).

tff(c_4597,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_4575])).

tff(c_7129,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4597])).

tff(c_7132,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_7129])).

tff(c_7136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_7132])).

tff(c_7137,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_4597])).

tff(c_7210,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7137])).

tff(c_7213,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_675,c_7210])).

tff(c_7220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_6311,c_7213])).

tff(c_7221,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_7137])).

tff(c_30,plain,
    ( ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_16,plain,(
    ! [B_19,A_17] :
      ( v4_tops_1(B_19,A_17)
      | ~ r1_tarski(B_19,k2_pre_topc(A_17,k1_tops_1(A_17,B_19)))
      | ~ r1_tarski(k1_tops_1(A_17,k2_pre_topc(A_17,B_19)),B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6370,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6298,c_16])).

tff(c_6445,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_207,c_6298,c_92,c_6370])).

tff(c_6446,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6445])).

tff(c_6486,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6311,c_6446])).

tff(c_7225,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7221,c_6486])).

tff(c_7241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7225])).

tff(c_7243,plain,(
    v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_7278,plain,(
    ! [A_222,B_223] :
      ( k1_tops_1(A_222,k1_tops_1(A_222,B_223)) = k1_tops_1(A_222,B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7284,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_7278])).

tff(c_7289,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7284])).

tff(c_7320,plain,(
    ! [B_226,A_227] :
      ( r1_tarski(B_226,k2_pre_topc(A_227,k1_tops_1(A_227,B_226)))
      | ~ v4_tops_1(B_226,A_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7325,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7289,c_7320])).

tff(c_7328,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7243,c_7325])).

tff(c_7395,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7328])).

tff(c_7407,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_7395])).

tff(c_7411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_7407])).

tff(c_7413,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7328])).

tff(c_7299,plain,(
    ! [A_224,B_225] :
      ( k2_pre_topc(A_224,k2_pre_topc(A_224,B_225)) = k2_pre_topc(A_224,B_225)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7305,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_7299])).

tff(c_7310,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7305])).

tff(c_7271,plain,(
    ! [A_220,B_221] :
      ( m1_subset_1(k2_pre_topc(A_220,B_221),k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7367,plain,(
    ! [A_232,B_233] :
      ( r1_tarski(k1_tops_1(A_232,k2_pre_topc(A_232,B_233)),k2_pre_topc(A_232,B_233))
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(resolution,[status(thm)],[c_7271,c_26])).

tff(c_7375,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7310,c_7367])).

tff(c_7380,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7310,c_7375])).

tff(c_7476,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7380])).

tff(c_7479,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_7476])).

tff(c_7483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_7479])).

tff(c_7485,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7380])).

tff(c_7567,plain,(
    ! [A_240,B_241,C_242] :
      ( r1_tarski(k2_pre_topc(A_240,B_241),k2_pre_topc(A_240,C_242))
      | ~ r1_tarski(B_241,C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7581,plain,(
    ! [B_241] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_241),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_241,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7310,c_7567])).

tff(c_7590,plain,(
    ! [B_241] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_241),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_241,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7485,c_7581])).

tff(c_7415,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7413,c_10])).

tff(c_7424,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7415])).

tff(c_7277,plain,(
    ! [A_220,B_221] :
      ( r1_tarski(k1_tops_1(A_220,k2_pre_topc(A_220,B_221)),k2_pre_topc(A_220,B_221))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(resolution,[status(thm)],[c_7271,c_26])).

tff(c_7446,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7424,c_7277])).

tff(c_7464,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7424,c_7446])).

tff(c_8228,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7464])).

tff(c_8259,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_8228])).

tff(c_8263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7413,c_8259])).

tff(c_8265,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7464])).

tff(c_7412,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_7328])).

tff(c_7852,plain,(
    ! [A_254,B_255,C_256] :
      ( r1_tarski(k1_tops_1(A_254,B_255),k1_tops_1(A_254,C_256))
      | ~ r1_tarski(B_255,C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7869,plain,(
    ! [C_256] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_256))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7289,c_7852])).

tff(c_7883,plain,(
    ! [C_256] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_256))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7413,c_7869])).

tff(c_7486,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(k1_tops_1(A_238,k2_pre_topc(A_238,B_239)),B_239)
      | ~ v4_tops_1(B_239,A_238)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ l1_pre_topc(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8523,plain,(
    ! [A_270,B_271] :
      ( k1_tops_1(A_270,k2_pre_topc(A_270,B_271)) = B_271
      | ~ r1_tarski(B_271,k1_tops_1(A_270,k2_pre_topc(A_270,B_271)))
      | ~ v4_tops_1(B_271,A_270)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(resolution,[status(thm)],[c_7486,c_2])).

tff(c_8530,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7883,c_8523])).

tff(c_8548,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8265,c_7412,c_36,c_7413,c_7243,c_8530])).

tff(c_8580,plain,(
    ! [C_33] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_33))
      | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8548,c_28])).

tff(c_8641,plain,(
    ! [C_272] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_272))
      | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),C_272)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8265,c_8580])).

tff(c_8645,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7590,c_8641])).

tff(c_8664,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7413,c_7485,c_8645])).

tff(c_8675,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_8664])).

tff(c_7254,plain,(
    ! [B_216,A_217] :
      ( r1_tarski(B_216,k2_pre_topc(A_217,B_216))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7256,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_7254])).

tff(c_7259,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7256])).

tff(c_7503,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7485,c_24])).

tff(c_7513,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7503])).

tff(c_7264,plain,(
    ! [A_218,B_219] :
      ( m1_subset_1(k1_tops_1(A_218,B_219),k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7269,plain,(
    ! [A_218,B_219] :
      ( r1_tarski(k1_tops_1(A_218,B_219),k2_pre_topc(A_218,k1_tops_1(A_218,B_219)))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(resolution,[status(thm)],[c_7264,c_12])).

tff(c_7532,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7513,c_7269])).

tff(c_7553,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7513,c_7532])).

tff(c_7979,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7553])).

tff(c_7982,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_7979])).

tff(c_7986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7485,c_7982])).

tff(c_7988,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7553])).

tff(c_7886,plain,(
    ! [C_257] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_257))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7413,c_7869])).

tff(c_8676,plain,(
    ! [C_273] :
      ( k1_tops_1('#skF_1',C_273) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1',C_273),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_7886,c_2])).

tff(c_8693,plain,(
    ! [B_31] :
      ( k1_tops_1('#skF_1',B_31) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_31)
      | ~ r1_tarski(B_31,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_8676])).

tff(c_8737,plain,(
    ! [B_274] :
      ( k1_tops_1('#skF_1',B_274) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_274)
      | ~ r1_tarski(B_274,'#skF_2')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_8693])).

tff(c_8743,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7988,c_8737])).

tff(c_8765,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7513,c_8743])).

tff(c_10262,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8765])).

tff(c_10369,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_10262])).

tff(c_10373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_10369])).

tff(c_10374,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_8765])).

tff(c_10388,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_10374])).

tff(c_10446,plain,
    ( ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_10388])).

tff(c_10453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_7485,c_7259,c_10446])).

tff(c_10454,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_10374])).

tff(c_8583,plain,(
    ! [B_31] :
      ( r1_tarski(k1_tops_1('#skF_1',B_31),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_31,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8548,c_28])).

tff(c_8780,plain,(
    ! [B_275] :
      ( r1_tarski(k1_tops_1('#skF_1',B_275),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_275,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8265,c_8583])).

tff(c_8802,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7513,c_8780])).

tff(c_8817,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7988,c_8802])).

tff(c_8820,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_8817])).

tff(c_10457,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10454,c_8820])).

tff(c_10470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7412,c_10457])).

tff(c_10471,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_8817])).

tff(c_10481,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_10471,c_2])).

tff(c_10485,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_10481])).

tff(c_10524,plain,
    ( ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_10485])).

tff(c_10531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_7485,c_7259,c_10524])).

tff(c_10532,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_10481])).

tff(c_7484,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7380])).

tff(c_10544,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10532,c_7484])).

tff(c_10553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8675,c_10544])).

tff(c_10555,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_8664])).

tff(c_7603,plain,(
    ! [B_244] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_244),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_244,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7485,c_7581])).

tff(c_7637,plain,(
    ! [B_247] :
      ( k2_pre_topc('#skF_1',B_247) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',B_247))
      | ~ r1_tarski(B_247,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_7603,c_2])).

tff(c_7648,plain,(
    ! [C_16] :
      ( k2_pre_topc('#skF_1',C_16) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(C_16,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_7637])).

tff(c_7674,plain,(
    ! [C_16] :
      ( k2_pre_topc('#skF_1',C_16) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(C_16,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_7648])).

tff(c_8274,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8265,c_7674])).

tff(c_8296,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7424,c_8274])).

tff(c_13125,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_8296])).

tff(c_13128,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_13125])).

tff(c_13132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_13128])).

tff(c_13133,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_8296])).

tff(c_13210,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_13133])).

tff(c_13213,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7590,c_13210])).

tff(c_13220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7413,c_10555,c_13213])).

tff(c_13221,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_13133])).

tff(c_10554,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_8664])).

tff(c_10559,plain,(
    ! [C_313] :
      ( k1_tops_1('#skF_1',C_313) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1',C_313),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_7886,c_2])).

tff(c_10576,plain,(
    ! [B_31] :
      ( k1_tops_1('#skF_1',B_31) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_31)
      | ~ r1_tarski(B_31,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_10559])).

tff(c_10642,plain,(
    ! [B_314] :
      ( k1_tops_1('#skF_1',B_314) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_314)
      | ~ r1_tarski(B_314,'#skF_2')
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_10576])).

tff(c_10648,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7988,c_10642])).

tff(c_10671,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10554,c_7513,c_10648])).

tff(c_10688,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_10671])).

tff(c_10724,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_10688])).

tff(c_10728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_10724])).

tff(c_10729,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_10671])).

tff(c_10628,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10554,c_2])).

tff(c_10629,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10628])).

tff(c_10741,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10729,c_10629])).

tff(c_10755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10741])).

tff(c_10756,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_10628])).

tff(c_7242,plain,(
    ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_8045,plain,(
    ! [B_261,A_262] :
      ( v4_tops_1(B_261,A_262)
      | ~ r1_tarski(B_261,k2_pre_topc(A_262,k1_tops_1(A_262,B_261)))
      | ~ r1_tarski(k1_tops_1(A_262,k2_pre_topc(A_262,B_261)),B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8065,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7310,c_8045])).

tff(c_8076,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7485,c_7484,c_8065])).

tff(c_8077,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_7242,c_8076])).

tff(c_10763,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10756,c_8077])).

tff(c_13279,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13221,c_10763])).

tff(c_13289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:10:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.59/3.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.59/3.31  
% 9.59/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.59/3.31  %$ v4_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 9.59/3.31  
% 9.59/3.31  %Foreground sorts:
% 9.59/3.31  
% 9.59/3.31  
% 9.59/3.31  %Background operators:
% 9.59/3.31  
% 9.59/3.31  
% 9.59/3.31  %Foreground operators:
% 9.59/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.59/3.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.59/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.59/3.31  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 9.59/3.31  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.59/3.31  tff('#skF_2', type, '#skF_2': $i).
% 9.59/3.31  tff('#skF_1', type, '#skF_1': $i).
% 9.59/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.59/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.59/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.59/3.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.59/3.31  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.59/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.59/3.31  
% 9.95/3.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.95/3.35  tff(f_116, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) => (v4_tops_1(k1_tops_1(A, B), A) & v4_tops_1(k2_pre_topc(A, B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_tops_1)).
% 9.95/3.35  tff(f_79, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 9.95/3.35  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.95/3.35  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 9.95/3.35  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 9.95/3.35  tff(f_85, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 9.95/3.35  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 9.95/3.35  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 9.95/3.35  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 9.95/3.35  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 9.95/3.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.95/3.35  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.95/3.35  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.95/3.35  tff(c_22, plain, (![A_20, B_21]: (m1_subset_1(k1_tops_1(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.95/3.35  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.95/3.35  tff(c_102, plain, (![A_48, B_49]: (k2_pre_topc(A_48, k2_pre_topc(A_48, B_49))=k2_pre_topc(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.95/3.35  tff(c_108, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_102])).
% 9.95/3.35  tff(c_113, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_108])).
% 9.95/3.35  tff(c_67, plain, (![A_42, B_43]: (m1_subset_1(k2_pre_topc(A_42, B_43), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.95/3.35  tff(c_26, plain, (![A_24, B_26]: (r1_tarski(k1_tops_1(A_24, B_26), B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.95/3.35  tff(c_137, plain, (![A_52, B_53]: (r1_tarski(k1_tops_1(A_52, k2_pre_topc(A_52, B_53)), k2_pre_topc(A_52, B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_67, c_26])).
% 9.95/3.35  tff(c_142, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_113, c_137])).
% 9.95/3.35  tff(c_148, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_113, c_142])).
% 9.95/3.35  tff(c_228, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_148])).
% 9.95/3.35  tff(c_231, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_228])).
% 9.95/3.35  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_231])).
% 9.95/3.35  tff(c_237, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_148])).
% 9.95/3.35  tff(c_81, plain, (![A_46, B_47]: (k1_tops_1(A_46, k1_tops_1(A_46, B_47))=k1_tops_1(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.95/3.35  tff(c_87, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_81])).
% 9.95/3.35  tff(c_92, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_87])).
% 9.95/3.35  tff(c_74, plain, (![A_44, B_45]: (m1_subset_1(k1_tops_1(A_44, B_45), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.95/3.35  tff(c_12, plain, (![B_9, A_7]: (r1_tarski(B_9, k2_pre_topc(A_7, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.95/3.35  tff(c_123, plain, (![A_50, B_51]: (r1_tarski(k1_tops_1(A_50, B_51), k2_pre_topc(A_50, k1_tops_1(A_50, B_51))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_74, c_12])).
% 9.95/3.35  tff(c_131, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_123])).
% 9.95/3.35  tff(c_136, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_92, c_131])).
% 9.95/3.35  tff(c_198, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_136])).
% 9.95/3.35  tff(c_201, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_198])).
% 9.95/3.35  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_201])).
% 9.95/3.35  tff(c_207, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_136])).
% 9.95/3.35  tff(c_47, plain, (![A_38, B_39]: (r1_tarski(k1_tops_1(A_38, B_39), B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.95/3.35  tff(c_49, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_47])).
% 9.95/3.35  tff(c_52, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_49])).
% 9.95/3.35  tff(c_14, plain, (![A_10, B_14, C_16]: (r1_tarski(k2_pre_topc(A_10, B_14), k2_pre_topc(A_10, C_16)) | ~r1_tarski(B_14, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.95/3.35  tff(c_32, plain, (v4_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.95/3.35  tff(c_18, plain, (![B_19, A_17]: (r1_tarski(B_19, k2_pre_topc(A_17, k1_tops_1(A_17, B_19))) | ~v4_tops_1(B_19, A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.35  tff(c_10, plain, (![A_5, B_6]: (k2_pre_topc(A_5, k2_pre_topc(A_5, B_6))=k2_pre_topc(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.95/3.35  tff(c_209, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_207, c_10])).
% 9.95/3.35  tff(c_218, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_209])).
% 9.95/3.35  tff(c_73, plain, (![A_42, B_43]: (r1_tarski(k1_tops_1(A_42, k2_pre_topc(A_42, B_43)), k2_pre_topc(A_42, B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_67, c_26])).
% 9.95/3.35  tff(c_290, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_218, c_73])).
% 9.95/3.35  tff(c_308, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_218, c_290])).
% 9.95/3.35  tff(c_771, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_308])).
% 9.95/3.35  tff(c_774, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_771])).
% 9.95/3.35  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_207, c_774])).
% 9.95/3.35  tff(c_780, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_308])).
% 9.95/3.35  tff(c_359, plain, (![A_62, B_63, C_64]: (r1_tarski(k2_pre_topc(A_62, B_63), k2_pre_topc(A_62, C_64)) | ~r1_tarski(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.95/3.35  tff(c_373, plain, (![B_63]: (r1_tarski(k2_pre_topc('#skF_1', B_63), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_63, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_359])).
% 9.95/3.35  tff(c_395, plain, (![B_66]: (r1_tarski(k2_pre_topc('#skF_1', B_66), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_66, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_237, c_373])).
% 9.95/3.35  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.95/3.35  tff(c_429, plain, (![B_69]: (k2_pre_topc('#skF_1', B_69)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', B_69)) | ~r1_tarski(B_69, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_395, c_2])).
% 9.95/3.35  tff(c_440, plain, (![C_16]: (k2_pre_topc('#skF_1', C_16)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(C_16, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_429])).
% 9.95/3.35  tff(c_466, plain, (![C_16]: (k2_pre_topc('#skF_1', C_16)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(C_16, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_440])).
% 9.95/3.35  tff(c_786, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_780, c_466])).
% 9.95/3.35  tff(c_806, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_786])).
% 9.95/3.35  tff(c_6201, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_806])).
% 9.95/3.35  tff(c_6257, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_6201])).
% 9.95/3.35  tff(c_6261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_6257])).
% 9.95/3.35  tff(c_6262, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_806])).
% 9.95/3.35  tff(c_6278, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_6262])).
% 9.95/3.35  tff(c_6287, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_6278])).
% 9.95/3.35  tff(c_6297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_207, c_34, c_52, c_6287])).
% 9.95/3.35  tff(c_6298, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_6262])).
% 9.95/3.35  tff(c_206, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_136])).
% 9.95/3.35  tff(c_6311, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6298, c_206])).
% 9.95/3.35  tff(c_644, plain, (![A_76, B_77, C_78]: (r1_tarski(k1_tops_1(A_76, B_77), k1_tops_1(A_76, C_78)) | ~r1_tarski(B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.95/3.35  tff(c_661, plain, (![C_78]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_78)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_644])).
% 9.95/3.35  tff(c_675, plain, (![C_78]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_78)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_207, c_661])).
% 9.95/3.35  tff(c_20, plain, (![A_17, B_19]: (r1_tarski(k1_tops_1(A_17, k2_pre_topc(A_17, B_19)), B_19) | ~v4_tops_1(B_19, A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.35  tff(c_24, plain, (![A_22, B_23]: (k1_tops_1(A_22, k1_tops_1(A_22, B_23))=k1_tops_1(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.95/3.35  tff(c_241, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_237, c_24])).
% 9.95/3.35  tff(c_251, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_241])).
% 9.95/3.35  tff(c_236, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_148])).
% 9.95/3.35  tff(c_835, plain, (![B_83, A_84]: (v4_tops_1(B_83, A_84) | ~r1_tarski(B_83, k2_pre_topc(A_84, k1_tops_1(A_84, B_83))) | ~r1_tarski(k1_tops_1(A_84, k2_pre_topc(A_84, B_83)), B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.35  tff(c_855, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_113, c_835])).
% 9.95/3.35  tff(c_867, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_237, c_236, c_855])).
% 9.95/3.35  tff(c_868, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_867])).
% 9.95/3.35  tff(c_3370, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_806])).
% 9.95/3.35  tff(c_3373, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_3370])).
% 9.95/3.35  tff(c_3377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_3373])).
% 9.95/3.35  tff(c_3378, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_806])).
% 9.95/3.35  tff(c_3440, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3378])).
% 9.95/3.35  tff(c_3446, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_3440])).
% 9.95/3.35  tff(c_3453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_207, c_34, c_52, c_3446])).
% 9.95/3.35  tff(c_3454, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_3378])).
% 9.95/3.35  tff(c_779, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_308])).
% 9.95/3.35  tff(c_849, plain, (v4_tops_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_218, c_835])).
% 9.95/3.35  tff(c_864, plain, (v4_tops_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_780, c_779, c_849])).
% 9.95/3.35  tff(c_1370, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))))), inference(splitLeft, [status(thm)], [c_864])).
% 9.95/3.35  tff(c_1417, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_1370])).
% 9.95/3.35  tff(c_1423, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_207, c_1417])).
% 9.95/3.35  tff(c_1547, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1423])).
% 9.95/3.35  tff(c_1550, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1547])).
% 9.95/3.35  tff(c_1554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_780, c_1550])).
% 9.95/3.35  tff(c_1555, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_1423])).
% 9.95/3.35  tff(c_1628, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_675, c_1555])).
% 9.95/3.35  tff(c_1635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_780, c_206, c_1628])).
% 9.95/3.35  tff(c_1637, plain, (r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))))), inference(splitRight, [status(thm)], [c_864])).
% 9.95/3.35  tff(c_3457, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3454, c_3454, c_1637])).
% 9.95/3.35  tff(c_3469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_868, c_3457])).
% 9.95/3.35  tff(c_3470, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_867])).
% 9.95/3.35  tff(c_382, plain, (![B_63]: (r1_tarski(k2_pre_topc('#skF_1', B_63), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_63, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_237, c_373])).
% 9.95/3.35  tff(c_189, plain, (![B_58, A_59]: (r1_tarski(B_58, k2_pre_topc(A_59, k1_tops_1(A_59, B_58))) | ~v4_tops_1(B_58, A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.35  tff(c_3481, plain, (![A_137, B_138]: (k2_pre_topc(A_137, k1_tops_1(A_137, B_138))=B_138 | ~r1_tarski(k2_pre_topc(A_137, k1_tops_1(A_137, B_138)), B_138) | ~v4_tops_1(B_138, A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_189, c_2])).
% 9.95/3.35  tff(c_3488, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_382, c_3481])).
% 9.95/3.35  tff(c_3503, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_36, c_237, c_3470, c_3488])).
% 9.95/3.35  tff(c_3509, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_3503])).
% 9.95/3.35  tff(c_3512, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_3509])).
% 9.95/3.35  tff(c_3516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_237, c_3512])).
% 9.95/3.35  tff(c_3518, plain, (m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_3503])).
% 9.95/3.35  tff(c_28, plain, (![A_27, B_31, C_33]: (r1_tarski(k1_tops_1(A_27, B_31), k1_tops_1(A_27, C_33)) | ~r1_tarski(B_31, C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.95/3.35  tff(c_678, plain, (![C_79]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_79)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_207, c_661])).
% 9.95/3.35  tff(c_4507, plain, (![C_159]: (k1_tops_1('#skF_1', C_159)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', C_159), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_678, c_2])).
% 9.95/3.35  tff(c_4518, plain, (![B_31]: (k1_tops_1('#skF_1', B_31)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_31) | ~r1_tarski(B_31, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_4507])).
% 9.95/3.35  tff(c_4572, plain, (![B_160]: (k1_tops_1('#skF_1', B_160)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_160) | ~r1_tarski(B_160, '#skF_2') | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4518])).
% 9.95/3.35  tff(c_4575, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_3518, c_4572])).
% 9.95/3.35  tff(c_4597, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_4575])).
% 9.95/3.35  tff(c_7129, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_4597])).
% 9.95/3.35  tff(c_7132, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_7129])).
% 9.95/3.35  tff(c_7136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_7132])).
% 9.95/3.35  tff(c_7137, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_4597])).
% 9.95/3.35  tff(c_7210, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_7137])).
% 9.95/3.35  tff(c_7213, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_675, c_7210])).
% 9.95/3.35  tff(c_7220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237, c_6311, c_7213])).
% 9.95/3.35  tff(c_7221, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_7137])).
% 9.95/3.35  tff(c_30, plain, (~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.95/3.35  tff(c_46, plain, (~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 9.95/3.35  tff(c_16, plain, (![B_19, A_17]: (v4_tops_1(B_19, A_17) | ~r1_tarski(B_19, k2_pre_topc(A_17, k1_tops_1(A_17, B_19))) | ~r1_tarski(k1_tops_1(A_17, k2_pre_topc(A_17, B_19)), B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.35  tff(c_6370, plain, (v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6298, c_16])).
% 9.95/3.35  tff(c_6445, plain, (v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_207, c_6298, c_92, c_6370])).
% 9.95/3.35  tff(c_6446, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_6445])).
% 9.95/3.35  tff(c_6486, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6311, c_6446])).
% 9.95/3.35  tff(c_7225, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7221, c_6486])).
% 9.95/3.35  tff(c_7241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7225])).
% 9.95/3.35  tff(c_7243, plain, (v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 9.95/3.35  tff(c_7278, plain, (![A_222, B_223]: (k1_tops_1(A_222, k1_tops_1(A_222, B_223))=k1_tops_1(A_222, B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.95/3.35  tff(c_7284, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_7278])).
% 9.95/3.35  tff(c_7289, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7284])).
% 9.95/3.35  tff(c_7320, plain, (![B_226, A_227]: (r1_tarski(B_226, k2_pre_topc(A_227, k1_tops_1(A_227, B_226))) | ~v4_tops_1(B_226, A_227) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.35  tff(c_7325, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7289, c_7320])).
% 9.95/3.35  tff(c_7328, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7243, c_7325])).
% 9.95/3.35  tff(c_7395, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7328])).
% 9.95/3.35  tff(c_7407, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_7395])).
% 9.95/3.35  tff(c_7411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_7407])).
% 9.95/3.35  tff(c_7413, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7328])).
% 9.95/3.35  tff(c_7299, plain, (![A_224, B_225]: (k2_pre_topc(A_224, k2_pre_topc(A_224, B_225))=k2_pre_topc(A_224, B_225) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.95/3.35  tff(c_7305, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_7299])).
% 9.95/3.35  tff(c_7310, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7305])).
% 9.95/3.35  tff(c_7271, plain, (![A_220, B_221]: (m1_subset_1(k2_pre_topc(A_220, B_221), k1_zfmisc_1(u1_struct_0(A_220))) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.95/3.35  tff(c_7367, plain, (![A_232, B_233]: (r1_tarski(k1_tops_1(A_232, k2_pre_topc(A_232, B_233)), k2_pre_topc(A_232, B_233)) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(resolution, [status(thm)], [c_7271, c_26])).
% 9.95/3.35  tff(c_7375, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7310, c_7367])).
% 9.95/3.35  tff(c_7380, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7310, c_7375])).
% 9.95/3.35  tff(c_7476, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7380])).
% 9.95/3.35  tff(c_7479, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_7476])).
% 9.95/3.35  tff(c_7483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_7479])).
% 9.95/3.35  tff(c_7485, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7380])).
% 9.95/3.35  tff(c_7567, plain, (![A_240, B_241, C_242]: (r1_tarski(k2_pre_topc(A_240, B_241), k2_pre_topc(A_240, C_242)) | ~r1_tarski(B_241, C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(u1_struct_0(A_240))) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.95/3.35  tff(c_7581, plain, (![B_241]: (r1_tarski(k2_pre_topc('#skF_1', B_241), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_241, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7310, c_7567])).
% 9.95/3.35  tff(c_7590, plain, (![B_241]: (r1_tarski(k2_pre_topc('#skF_1', B_241), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_241, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7485, c_7581])).
% 9.95/3.35  tff(c_7415, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7413, c_10])).
% 9.95/3.35  tff(c_7424, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7415])).
% 9.95/3.35  tff(c_7277, plain, (![A_220, B_221]: (r1_tarski(k1_tops_1(A_220, k2_pre_topc(A_220, B_221)), k2_pre_topc(A_220, B_221)) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(resolution, [status(thm)], [c_7271, c_26])).
% 9.95/3.35  tff(c_7446, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7424, c_7277])).
% 9.95/3.35  tff(c_7464, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7424, c_7446])).
% 9.95/3.35  tff(c_8228, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7464])).
% 9.95/3.35  tff(c_8259, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_8228])).
% 9.95/3.35  tff(c_8263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_7413, c_8259])).
% 9.95/3.35  tff(c_8265, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7464])).
% 9.95/3.35  tff(c_7412, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_7328])).
% 9.95/3.35  tff(c_7852, plain, (![A_254, B_255, C_256]: (r1_tarski(k1_tops_1(A_254, B_255), k1_tops_1(A_254, C_256)) | ~r1_tarski(B_255, C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(u1_struct_0(A_254))) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.95/3.35  tff(c_7869, plain, (![C_256]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_256)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7289, c_7852])).
% 9.95/3.35  tff(c_7883, plain, (![C_256]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_256)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7413, c_7869])).
% 9.95/3.35  tff(c_7486, plain, (![A_238, B_239]: (r1_tarski(k1_tops_1(A_238, k2_pre_topc(A_238, B_239)), B_239) | ~v4_tops_1(B_239, A_238) | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0(A_238))) | ~l1_pre_topc(A_238))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.35  tff(c_8523, plain, (![A_270, B_271]: (k1_tops_1(A_270, k2_pre_topc(A_270, B_271))=B_271 | ~r1_tarski(B_271, k1_tops_1(A_270, k2_pre_topc(A_270, B_271))) | ~v4_tops_1(B_271, A_270) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(resolution, [status(thm)], [c_7486, c_2])).
% 9.95/3.35  tff(c_8530, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7883, c_8523])).
% 9.95/3.35  tff(c_8548, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8265, c_7412, c_36, c_7413, c_7243, c_8530])).
% 9.95/3.35  tff(c_8580, plain, (![C_33]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_33)) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8548, c_28])).
% 9.95/3.35  tff(c_8641, plain, (![C_272]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_272)) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), C_272) | ~m1_subset_1(C_272, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8265, c_8580])).
% 9.95/3.35  tff(c_8645, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7590, c_8641])).
% 9.95/3.35  tff(c_8664, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7413, c_7485, c_8645])).
% 9.95/3.35  tff(c_8675, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_8664])).
% 9.95/3.35  tff(c_7254, plain, (![B_216, A_217]: (r1_tarski(B_216, k2_pre_topc(A_217, B_216)) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.95/3.35  tff(c_7256, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_7254])).
% 9.95/3.35  tff(c_7259, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7256])).
% 9.95/3.35  tff(c_7503, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7485, c_24])).
% 9.95/3.35  tff(c_7513, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7503])).
% 9.95/3.35  tff(c_7264, plain, (![A_218, B_219]: (m1_subset_1(k1_tops_1(A_218, B_219), k1_zfmisc_1(u1_struct_0(A_218))) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.95/3.35  tff(c_7269, plain, (![A_218, B_219]: (r1_tarski(k1_tops_1(A_218, B_219), k2_pre_topc(A_218, k1_tops_1(A_218, B_219))) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(resolution, [status(thm)], [c_7264, c_12])).
% 9.95/3.35  tff(c_7532, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7513, c_7269])).
% 9.95/3.35  tff(c_7553, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7513, c_7532])).
% 9.95/3.35  tff(c_7979, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7553])).
% 9.95/3.35  tff(c_7982, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_7979])).
% 9.95/3.35  tff(c_7986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_7485, c_7982])).
% 9.95/3.35  tff(c_7988, plain, (m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7553])).
% 9.95/3.35  tff(c_7886, plain, (![C_257]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_257)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7413, c_7869])).
% 9.95/3.35  tff(c_8676, plain, (![C_273]: (k1_tops_1('#skF_1', C_273)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', C_273), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_7886, c_2])).
% 9.95/3.35  tff(c_8693, plain, (![B_31]: (k1_tops_1('#skF_1', B_31)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_31) | ~r1_tarski(B_31, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_8676])).
% 9.95/3.35  tff(c_8737, plain, (![B_274]: (k1_tops_1('#skF_1', B_274)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_274) | ~r1_tarski(B_274, '#skF_2') | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_8693])).
% 9.95/3.35  tff(c_8743, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_7988, c_8737])).
% 9.95/3.35  tff(c_8765, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7513, c_8743])).
% 9.95/3.35  tff(c_10262, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_8765])).
% 9.95/3.35  tff(c_10369, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_10262])).
% 9.95/3.35  tff(c_10373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_10369])).
% 9.95/3.35  tff(c_10374, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_8765])).
% 9.95/3.35  tff(c_10388, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_10374])).
% 9.95/3.35  tff(c_10446, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_10388])).
% 9.95/3.35  tff(c_10453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_7485, c_7259, c_10446])).
% 9.95/3.35  tff(c_10454, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_10374])).
% 9.95/3.35  tff(c_8583, plain, (![B_31]: (r1_tarski(k1_tops_1('#skF_1', B_31), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_31, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8548, c_28])).
% 9.95/3.35  tff(c_8780, plain, (![B_275]: (r1_tarski(k1_tops_1('#skF_1', B_275), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_275, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8265, c_8583])).
% 9.95/3.35  tff(c_8802, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_7513, c_8780])).
% 9.95/3.35  tff(c_8817, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7988, c_8802])).
% 9.95/3.35  tff(c_8820, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_8817])).
% 9.95/3.35  tff(c_10457, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10454, c_8820])).
% 9.95/3.35  tff(c_10470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7412, c_10457])).
% 9.95/3.35  tff(c_10471, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_8817])).
% 9.95/3.35  tff(c_10481, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_10471, c_2])).
% 9.95/3.35  tff(c_10485, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_10481])).
% 9.95/3.35  tff(c_10524, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_10485])).
% 9.95/3.35  tff(c_10531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_7485, c_7259, c_10524])).
% 9.95/3.35  tff(c_10532, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_10481])).
% 9.95/3.35  tff(c_7484, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_7380])).
% 9.95/3.35  tff(c_10544, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10532, c_7484])).
% 9.95/3.35  tff(c_10553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8675, c_10544])).
% 9.95/3.35  tff(c_10555, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_8664])).
% 9.95/3.35  tff(c_7603, plain, (![B_244]: (r1_tarski(k2_pre_topc('#skF_1', B_244), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_244, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7485, c_7581])).
% 9.95/3.35  tff(c_7637, plain, (![B_247]: (k2_pre_topc('#skF_1', B_247)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', B_247)) | ~r1_tarski(B_247, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_7603, c_2])).
% 9.95/3.35  tff(c_7648, plain, (![C_16]: (k2_pre_topc('#skF_1', C_16)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(C_16, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_7637])).
% 9.95/3.35  tff(c_7674, plain, (![C_16]: (k2_pre_topc('#skF_1', C_16)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(C_16, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_7648])).
% 9.95/3.35  tff(c_8274, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_8265, c_7674])).
% 9.95/3.35  tff(c_8296, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7424, c_8274])).
% 9.95/3.35  tff(c_13125, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_8296])).
% 9.95/3.35  tff(c_13128, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_13125])).
% 9.95/3.35  tff(c_13132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_13128])).
% 9.95/3.35  tff(c_13133, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_8296])).
% 9.95/3.35  tff(c_13210, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_13133])).
% 9.95/3.35  tff(c_13213, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7590, c_13210])).
% 9.95/3.35  tff(c_13220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7413, c_10555, c_13213])).
% 9.95/3.35  tff(c_13221, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_13133])).
% 9.95/3.35  tff(c_10554, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_8664])).
% 9.95/3.35  tff(c_10559, plain, (![C_313]: (k1_tops_1('#skF_1', C_313)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', C_313), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_7886, c_2])).
% 9.95/3.35  tff(c_10576, plain, (![B_31]: (k1_tops_1('#skF_1', B_31)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_31) | ~r1_tarski(B_31, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_10559])).
% 9.95/3.35  tff(c_10642, plain, (![B_314]: (k1_tops_1('#skF_1', B_314)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_314) | ~r1_tarski(B_314, '#skF_2') | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_10576])).
% 9.95/3.35  tff(c_10648, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_7988, c_10642])).
% 9.95/3.35  tff(c_10671, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10554, c_7513, c_10648])).
% 9.95/3.35  tff(c_10688, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_10671])).
% 9.95/3.35  tff(c_10724, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_10688])).
% 9.95/3.35  tff(c_10728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_10724])).
% 9.95/3.35  tff(c_10729, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_10671])).
% 9.95/3.35  tff(c_10628, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10554, c_2])).
% 9.95/3.35  tff(c_10629, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_10628])).
% 9.95/3.35  tff(c_10741, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10729, c_10629])).
% 9.95/3.35  tff(c_10755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10741])).
% 9.95/3.35  tff(c_10756, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_10628])).
% 9.95/3.35  tff(c_7242, plain, (~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 9.95/3.35  tff(c_8045, plain, (![B_261, A_262]: (v4_tops_1(B_261, A_262) | ~r1_tarski(B_261, k2_pre_topc(A_262, k1_tops_1(A_262, B_261))) | ~r1_tarski(k1_tops_1(A_262, k2_pre_topc(A_262, B_261)), B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.35  tff(c_8065, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7310, c_8045])).
% 9.95/3.35  tff(c_8076, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7485, c_7484, c_8065])).
% 9.95/3.35  tff(c_8077, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_7242, c_8076])).
% 9.95/3.35  tff(c_10763, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10756, c_8077])).
% 9.95/3.35  tff(c_13279, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13221, c_10763])).
% 9.95/3.35  tff(c_13289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13279])).
% 9.95/3.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.95/3.35  
% 9.95/3.35  Inference rules
% 9.95/3.35  ----------------------
% 9.95/3.35  #Ref     : 0
% 9.95/3.35  #Sup     : 2812
% 9.95/3.35  #Fact    : 0
% 9.95/3.35  #Define  : 0
% 9.95/3.35  #Split   : 48
% 9.95/3.35  #Chain   : 0
% 9.95/3.35  #Close   : 0
% 9.95/3.35  
% 9.95/3.35  Ordering : KBO
% 9.95/3.35  
% 9.95/3.35  Simplification rules
% 9.95/3.35  ----------------------
% 9.95/3.35  #Subsume      : 581
% 9.95/3.35  #Demod        : 4578
% 9.95/3.35  #Tautology    : 1046
% 9.95/3.35  #SimpNegUnit  : 14
% 9.95/3.35  #BackRed      : 100
% 9.95/3.35  
% 9.95/3.35  #Partial instantiations: 0
% 9.95/3.35  #Strategies tried      : 1
% 9.95/3.35  
% 9.95/3.35  Timing (in seconds)
% 9.95/3.35  ----------------------
% 9.95/3.36  Preprocessing        : 0.31
% 9.95/3.36  Parsing              : 0.17
% 9.95/3.36  CNF conversion       : 0.02
% 9.95/3.36  Main loop            : 2.24
% 9.95/3.36  Inferencing          : 0.64
% 9.95/3.36  Reduction            : 0.82
% 9.95/3.36  Demodulation         : 0.60
% 9.95/3.36  BG Simplification    : 0.09
% 9.95/3.36  Subsumption          : 0.58
% 9.95/3.36  Abstraction          : 0.14
% 9.95/3.36  MUC search           : 0.00
% 9.95/3.36  Cooper               : 0.00
% 9.95/3.36  Total                : 2.65
% 9.95/3.36  Index Insertion      : 0.00
% 9.95/3.36  Index Deletion       : 0.00
% 9.95/3.36  Index Matching       : 0.00
% 9.95/3.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
