%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:15 EST 2020

% Result     : Theorem 10.94s
% Output     : CNFRefutation 10.94s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 170 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 379 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1109,plain,(
    ! [A_80,B_81] :
      ( k2_pre_topc(A_80,k1_tops_1(A_80,B_81)) = B_81
      | ~ v5_tops_1(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1115,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1109])).

tff(c_1120,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_1115])).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1121,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1120,c_24])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_23,B_25] :
      ( r1_tarski(k2_tops_1(A_23,k2_pre_topc(A_23,B_25)),k2_tops_1(A_23,B_25))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1125,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_22])).

tff(c_1129,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1125])).

tff(c_2120,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1129])).

tff(c_2123,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_2120])).

tff(c_2127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2123])).

tff(c_2129,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1129])).

tff(c_20,plain,(
    ! [A_20,B_22] :
      ( k4_subset_1(u1_struct_0(A_20),B_22,k2_tops_1(A_20,B_22)) = k2_pre_topc(A_20,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2131,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2129,c_20])).

tff(c_2147,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1120,c_2131])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_363,plain,(
    ! [A_61,B_62,C_63] :
      ( k4_subset_1(A_61,B_62,C_63) = k2_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2733,plain,(
    ! [A_135,B_136,B_137] :
      ( k4_subset_1(u1_struct_0(A_135),B_136,k2_tops_1(A_135,B_137)) = k2_xboole_0(B_136,k2_tops_1(A_135,B_137))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_18,c_363])).

tff(c_2745,plain,(
    ! [A_16,B_17,B_137] :
      ( k4_subset_1(u1_struct_0(A_16),k1_tops_1(A_16,B_17),k2_tops_1(A_16,B_137)) = k2_xboole_0(k1_tops_1(A_16,B_17),k2_tops_1(A_16,B_137))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_2733])).

tff(c_28257,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2'
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2147,c_2745])).

tff(c_28270,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2129,c_28257])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_655,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k2_tops_1(A_71,k2_pre_topc(A_71,B_72)),k2_tops_1(A_71,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_658,plain,(
    ! [A_71,B_72] :
      ( k2_xboole_0(k2_tops_1(A_71,k2_pre_topc(A_71,B_72)),k2_tops_1(A_71,B_72)) = k2_tops_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_655,c_6])).

tff(c_2276,plain,(
    ! [A_121,B_122] :
      ( k2_xboole_0(k2_tops_1(A_121,B_122),k2_tops_1(A_121,k2_pre_topc(A_121,B_122))) = k2_tops_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_658])).

tff(c_2372,plain,
    ( k2_xboole_0(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_2276])).

tff(c_2392,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2129,c_2,c_2372])).

tff(c_32,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [A_30,B_29] : r1_tarski(A_30,k2_xboole_0(B_29,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_90,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(k2_xboole_0(A_35,B_37),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_35,B_29,B_37] : r1_tarski(A_35,k2_xboole_0(B_29,k2_xboole_0(A_35,B_37))) ),
    inference(resolution,[status(thm)],[c_47,c_90])).

tff(c_2471,plain,(
    ! [B_29] : r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(B_29,k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2392,c_105])).

tff(c_28370,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28270,c_2471])).

tff(c_28527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1121,c_28370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:51:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.94/5.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/5.05  
% 10.94/5.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/5.05  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 10.94/5.05  
% 10.94/5.05  %Foreground sorts:
% 10.94/5.05  
% 10.94/5.05  
% 10.94/5.05  %Background operators:
% 10.94/5.05  
% 10.94/5.05  
% 10.94/5.05  %Foreground operators:
% 10.94/5.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.94/5.05  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.94/5.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.94/5.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.94/5.05  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.94/5.05  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.94/5.05  tff('#skF_2', type, '#skF_2': $i).
% 10.94/5.05  tff('#skF_1', type, '#skF_1': $i).
% 10.94/5.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.94/5.05  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 10.94/5.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.94/5.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.94/5.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.94/5.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.94/5.05  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.94/5.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.94/5.05  
% 10.94/5.06  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 10.94/5.06  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 10.94/5.06  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 10.94/5.06  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 10.94/5.06  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.94/5.06  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 10.94/5.06  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.94/5.06  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.94/5.06  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.94/5.06  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.94/5.06  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 10.94/5.06  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.94/5.06  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.94/5.06  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.94/5.06  tff(c_1109, plain, (![A_80, B_81]: (k2_pre_topc(A_80, k1_tops_1(A_80, B_81))=B_81 | ~v5_tops_1(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.94/5.06  tff(c_1115, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1109])).
% 10.94/5.06  tff(c_1120, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_1115])).
% 10.94/5.06  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.94/5.06  tff(c_1121, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1120, c_24])).
% 10.94/5.06  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.94/5.06  tff(c_22, plain, (![A_23, B_25]: (r1_tarski(k2_tops_1(A_23, k2_pre_topc(A_23, B_25)), k2_tops_1(A_23, B_25)) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.94/5.06  tff(c_1125, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1120, c_22])).
% 10.94/5.06  tff(c_1129, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1125])).
% 10.94/5.06  tff(c_2120, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1129])).
% 10.94/5.06  tff(c_2123, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_2120])).
% 10.94/5.06  tff(c_2127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2123])).
% 10.94/5.06  tff(c_2129, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1129])).
% 10.94/5.06  tff(c_20, plain, (![A_20, B_22]: (k4_subset_1(u1_struct_0(A_20), B_22, k2_tops_1(A_20, B_22))=k2_pre_topc(A_20, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.94/5.06  tff(c_2131, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2129, c_20])).
% 10.94/5.06  tff(c_2147, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1120, c_2131])).
% 10.94/5.06  tff(c_18, plain, (![A_18, B_19]: (m1_subset_1(k2_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.94/5.06  tff(c_363, plain, (![A_61, B_62, C_63]: (k4_subset_1(A_61, B_62, C_63)=k2_xboole_0(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.94/5.06  tff(c_2733, plain, (![A_135, B_136, B_137]: (k4_subset_1(u1_struct_0(A_135), B_136, k2_tops_1(A_135, B_137))=k2_xboole_0(B_136, k2_tops_1(A_135, B_137)) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_18, c_363])).
% 10.94/5.06  tff(c_2745, plain, (![A_16, B_17, B_137]: (k4_subset_1(u1_struct_0(A_16), k1_tops_1(A_16, B_17), k2_tops_1(A_16, B_137))=k2_xboole_0(k1_tops_1(A_16, B_17), k2_tops_1(A_16, B_137)) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_16, c_2733])).
% 10.94/5.06  tff(c_28257, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2' | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2147, c_2745])).
% 10.94/5.06  tff(c_28270, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2129, c_28257])).
% 10.94/5.06  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.94/5.06  tff(c_655, plain, (![A_71, B_72]: (r1_tarski(k2_tops_1(A_71, k2_pre_topc(A_71, B_72)), k2_tops_1(A_71, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.94/5.06  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.94/5.06  tff(c_658, plain, (![A_71, B_72]: (k2_xboole_0(k2_tops_1(A_71, k2_pre_topc(A_71, B_72)), k2_tops_1(A_71, B_72))=k2_tops_1(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_655, c_6])).
% 10.94/5.06  tff(c_2276, plain, (![A_121, B_122]: (k2_xboole_0(k2_tops_1(A_121, B_122), k2_tops_1(A_121, k2_pre_topc(A_121, B_122)))=k2_tops_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_658])).
% 10.94/5.06  tff(c_2372, plain, (k2_xboole_0(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1120, c_2276])).
% 10.94/5.06  tff(c_2392, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2129, c_2, c_2372])).
% 10.94/5.06  tff(c_32, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.94/5.06  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.94/5.06  tff(c_47, plain, (![A_30, B_29]: (r1_tarski(A_30, k2_xboole_0(B_29, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_8])).
% 10.94/5.06  tff(c_90, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(k2_xboole_0(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.94/5.06  tff(c_105, plain, (![A_35, B_29, B_37]: (r1_tarski(A_35, k2_xboole_0(B_29, k2_xboole_0(A_35, B_37))))), inference(resolution, [status(thm)], [c_47, c_90])).
% 10.94/5.06  tff(c_2471, plain, (![B_29]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(B_29, k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_2392, c_105])).
% 10.94/5.06  tff(c_28370, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28270, c_2471])).
% 10.94/5.06  tff(c_28527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1121, c_28370])).
% 10.94/5.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/5.06  
% 10.94/5.06  Inference rules
% 10.94/5.06  ----------------------
% 10.94/5.06  #Ref     : 0
% 10.94/5.06  #Sup     : 6801
% 10.94/5.06  #Fact    : 0
% 10.94/5.07  #Define  : 0
% 10.94/5.07  #Split   : 3
% 10.94/5.07  #Chain   : 0
% 10.94/5.07  #Close   : 0
% 10.94/5.07  
% 10.94/5.07  Ordering : KBO
% 10.94/5.07  
% 10.94/5.07  Simplification rules
% 10.94/5.07  ----------------------
% 10.94/5.07  #Subsume      : 485
% 10.94/5.07  #Demod        : 5422
% 10.94/5.07  #Tautology    : 3974
% 10.94/5.07  #SimpNegUnit  : 1
% 10.94/5.07  #BackRed      : 2
% 10.94/5.07  
% 10.94/5.07  #Partial instantiations: 0
% 10.94/5.07  #Strategies tried      : 1
% 10.94/5.07  
% 10.94/5.07  Timing (in seconds)
% 10.94/5.07  ----------------------
% 10.94/5.07  Preprocessing        : 0.31
% 10.94/5.07  Parsing              : 0.16
% 10.94/5.07  CNF conversion       : 0.02
% 10.94/5.07  Main loop            : 4.00
% 10.94/5.07  Inferencing          : 0.67
% 10.94/5.07  Reduction            : 2.47
% 10.94/5.07  Demodulation         : 2.27
% 10.94/5.07  BG Simplification    : 0.08
% 10.94/5.07  Subsumption          : 0.60
% 10.94/5.07  Abstraction          : 0.12
% 10.94/5.07  MUC search           : 0.00
% 10.94/5.07  Cooper               : 0.00
% 10.94/5.07  Total                : 4.34
% 10.94/5.07  Index Insertion      : 0.00
% 10.94/5.07  Index Deletion       : 0.00
% 10.94/5.07  Index Matching       : 0.00
% 10.94/5.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
