%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:17 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 156 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 348 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_232,plain,(
    ! [A_72,B_73] :
      ( k2_pre_topc(A_72,k1_tops_1(A_72,B_73)) = B_73
      | ~ v5_tops_1(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_238,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_232])).

tff(c_243,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_238])).

tff(c_28,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_244,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_28])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_399,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k2_tops_1(A_93,k2_pre_topc(A_93,B_94)),k2_tops_1(A_93,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_408,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_399])).

tff(c_413,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_408])).

tff(c_1008,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_1011,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1008])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1011])).

tff(c_1017,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_179,plain,(
    ! [A_61,B_62,C_63] :
      ( k4_subset_1(A_61,B_62,C_63) = k2_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2029,plain,(
    ! [A_263,B_264,B_265] :
      ( k4_subset_1(u1_struct_0(A_263),B_264,k2_tops_1(A_263,B_265)) = k2_xboole_0(B_264,k2_tops_1(A_263,B_265))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(resolution,[status(thm)],[c_22,c_179])).

tff(c_4674,plain,(
    ! [A_420,B_421,B_422] :
      ( k4_subset_1(u1_struct_0(A_420),k1_tops_1(A_420,B_421),k2_tops_1(A_420,B_422)) = k2_xboole_0(k1_tops_1(A_420,B_421),k2_tops_1(A_420,B_422))
      | ~ m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0(A_420)))
      | ~ m1_subset_1(B_421,k1_zfmisc_1(u1_struct_0(A_420)))
      | ~ l1_pre_topc(A_420) ) ),
    inference(resolution,[status(thm)],[c_20,c_2029])).

tff(c_24,plain,(
    ! [A_21,B_23] :
      ( k4_subset_1(u1_struct_0(A_21),B_23,k2_tops_1(A_21,B_23)) = k2_pre_topc(A_21,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1022,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1017,c_24])).

tff(c_1036,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_243,c_1022])).

tff(c_4684,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2'
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4674,c_1036])).

tff(c_4696,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1017,c_4684])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1016,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(A_36,k2_xboole_0(B_37,C_38))
      | ~ r1_tarski(k4_xboole_0(A_36,B_37),C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(B_37,k4_xboole_0(A_36,B_37))) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_65,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(B_42,A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_61])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_47,B_48,A_49] :
      ( r1_tarski(A_47,k2_xboole_0(B_48,A_49))
      | ~ r1_tarski(A_47,A_49) ) ),
    inference(resolution,[status(thm)],[c_65,c_8])).

tff(c_122,plain,(
    ! [A_3,B_48,A_49,A_47] :
      ( r1_tarski(A_3,k2_xboole_0(B_48,A_49))
      | ~ r1_tarski(A_3,A_47)
      | ~ r1_tarski(A_47,A_49) ) ),
    inference(resolution,[status(thm)],[c_109,c_8])).

tff(c_2704,plain,(
    ! [B_304,A_305] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(B_304,A_305))
      | ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),A_305) ) ),
    inference(resolution,[status(thm)],[c_1016,c_122])).

tff(c_2781,plain,(
    ! [B_304] : r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(B_304,k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_6,c_2704])).

tff(c_4740,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4696,c_2781])).

tff(c_4839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_4740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:03:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.28  
% 6.19/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.28  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.19/2.28  
% 6.19/2.28  %Foreground sorts:
% 6.19/2.28  
% 6.19/2.28  
% 6.19/2.28  %Background operators:
% 6.19/2.28  
% 6.19/2.28  
% 6.19/2.28  %Foreground operators:
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.19/2.28  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.19/2.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.19/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.19/2.28  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.19/2.28  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.19/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.19/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.19/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.19/2.28  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.19/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.19/2.28  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.19/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.19/2.28  
% 6.19/2.29  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 6.19/2.29  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 6.19/2.29  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.19/2.29  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 6.19/2.29  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.19/2.29  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.19/2.29  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 6.19/2.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.19/2.29  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.19/2.29  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 6.19/2.29  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.19/2.29  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.19/2.29  tff(c_30, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.19/2.29  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.19/2.29  tff(c_232, plain, (![A_72, B_73]: (k2_pre_topc(A_72, k1_tops_1(A_72, B_73))=B_73 | ~v5_tops_1(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.19/2.29  tff(c_238, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_232])).
% 6.19/2.29  tff(c_243, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_238])).
% 6.19/2.29  tff(c_28, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.19/2.29  tff(c_244, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_28])).
% 6.19/2.29  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(k1_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.19/2.29  tff(c_399, plain, (![A_93, B_94]: (r1_tarski(k2_tops_1(A_93, k2_pre_topc(A_93, B_94)), k2_tops_1(A_93, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.19/2.29  tff(c_408, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_243, c_399])).
% 6.19/2.29  tff(c_413, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_408])).
% 6.19/2.29  tff(c_1008, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_413])).
% 6.19/2.29  tff(c_1011, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1008])).
% 6.19/2.29  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1011])).
% 6.19/2.29  tff(c_1017, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_413])).
% 6.19/2.29  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.19/2.29  tff(c_179, plain, (![A_61, B_62, C_63]: (k4_subset_1(A_61, B_62, C_63)=k2_xboole_0(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.19/2.29  tff(c_2029, plain, (![A_263, B_264, B_265]: (k4_subset_1(u1_struct_0(A_263), B_264, k2_tops_1(A_263, B_265))=k2_xboole_0(B_264, k2_tops_1(A_263, B_265)) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(resolution, [status(thm)], [c_22, c_179])).
% 6.19/2.29  tff(c_4674, plain, (![A_420, B_421, B_422]: (k4_subset_1(u1_struct_0(A_420), k1_tops_1(A_420, B_421), k2_tops_1(A_420, B_422))=k2_xboole_0(k1_tops_1(A_420, B_421), k2_tops_1(A_420, B_422)) | ~m1_subset_1(B_422, k1_zfmisc_1(u1_struct_0(A_420))) | ~m1_subset_1(B_421, k1_zfmisc_1(u1_struct_0(A_420))) | ~l1_pre_topc(A_420))), inference(resolution, [status(thm)], [c_20, c_2029])).
% 6.19/2.29  tff(c_24, plain, (![A_21, B_23]: (k4_subset_1(u1_struct_0(A_21), B_23, k2_tops_1(A_21, B_23))=k2_pre_topc(A_21, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.19/2.29  tff(c_1022, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1017, c_24])).
% 6.19/2.29  tff(c_1036, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_243, c_1022])).
% 6.19/2.29  tff(c_4684, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2' | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4674, c_1036])).
% 6.19/2.29  tff(c_4696, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1017, c_4684])).
% 6.19/2.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.19/2.29  tff(c_1016, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_413])).
% 6.19/2.29  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.19/2.29  tff(c_57, plain, (![A_36, B_37, C_38]: (r1_tarski(A_36, k2_xboole_0(B_37, C_38)) | ~r1_tarski(k4_xboole_0(A_36, B_37), C_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.19/2.29  tff(c_61, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(B_37, k4_xboole_0(A_36, B_37))))), inference(resolution, [status(thm)], [c_6, c_57])).
% 6.19/2.29  tff(c_65, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(B_42, A_41)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_61])).
% 6.19/2.29  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.19/2.29  tff(c_109, plain, (![A_47, B_48, A_49]: (r1_tarski(A_47, k2_xboole_0(B_48, A_49)) | ~r1_tarski(A_47, A_49))), inference(resolution, [status(thm)], [c_65, c_8])).
% 6.19/2.29  tff(c_122, plain, (![A_3, B_48, A_49, A_47]: (r1_tarski(A_3, k2_xboole_0(B_48, A_49)) | ~r1_tarski(A_3, A_47) | ~r1_tarski(A_47, A_49))), inference(resolution, [status(thm)], [c_109, c_8])).
% 6.19/2.29  tff(c_2704, plain, (![B_304, A_305]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(B_304, A_305)) | ~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), A_305))), inference(resolution, [status(thm)], [c_1016, c_122])).
% 6.19/2.29  tff(c_2781, plain, (![B_304]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(B_304, k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))))), inference(resolution, [status(thm)], [c_6, c_2704])).
% 6.19/2.29  tff(c_4740, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4696, c_2781])).
% 6.19/2.29  tff(c_4839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_4740])).
% 6.19/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.29  
% 6.19/2.29  Inference rules
% 6.19/2.29  ----------------------
% 6.19/2.29  #Ref     : 0
% 6.19/2.29  #Sup     : 1243
% 6.19/2.29  #Fact    : 0
% 6.19/2.29  #Define  : 0
% 6.19/2.29  #Split   : 5
% 6.19/2.29  #Chain   : 0
% 6.19/2.29  #Close   : 0
% 6.19/2.29  
% 6.19/2.29  Ordering : KBO
% 6.19/2.29  
% 6.19/2.29  Simplification rules
% 6.19/2.29  ----------------------
% 6.19/2.29  #Subsume      : 47
% 6.19/2.29  #Demod        : 169
% 6.19/2.29  #Tautology    : 130
% 6.19/2.29  #SimpNegUnit  : 2
% 6.19/2.29  #BackRed      : 1
% 6.19/2.29  
% 6.19/2.29  #Partial instantiations: 0
% 6.19/2.29  #Strategies tried      : 1
% 6.19/2.29  
% 6.19/2.29  Timing (in seconds)
% 6.19/2.29  ----------------------
% 6.19/2.29  Preprocessing        : 0.31
% 6.19/2.29  Parsing              : 0.17
% 6.19/2.29  CNF conversion       : 0.02
% 6.19/2.29  Main loop            : 1.23
% 6.19/2.29  Inferencing          : 0.35
% 6.19/2.30  Reduction            : 0.39
% 6.19/2.30  Demodulation         : 0.30
% 6.19/2.30  BG Simplification    : 0.05
% 6.19/2.30  Subsumption          : 0.35
% 6.19/2.30  Abstraction          : 0.06
% 6.19/2.30  MUC search           : 0.00
% 6.19/2.30  Cooper               : 0.00
% 6.19/2.30  Total                : 1.57
% 6.19/2.30  Index Insertion      : 0.00
% 6.19/2.30  Index Deletion       : 0.00
% 6.19/2.30  Index Matching       : 0.00
% 6.19/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
