%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:07 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 162 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  116 ( 378 expanded)
%              Number of equality atoms :   25 (  77 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k5_setfam_1 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(A),C))
                 => B = k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(k1_tops_2(A,B,C),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                 => ( r1_tarski(B,k5_setfam_1(u1_struct_0(A),D))
                   => r1_tarski(k9_subset_1(u1_struct_0(A),B,C),k5_setfam_1(u1_struct_0(k1_pre_topc(A,C)),k1_tops_2(A,C,D))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tops_2)).

tff(f_39,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_221,plain,(
    ! [A_73,B_74] :
      ( u1_struct_0(k1_pre_topc(A_73,B_74)) = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_228,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_221])).

tff(c_232,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_228])).

tff(c_479,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1(k1_tops_2(A_95,B_96,C_97),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_95,B_96)))))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95))))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_742,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_tarski(k1_tops_2(A_121,B_122,C_123),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_121,B_122))))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_121))))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_479,c_20])).

tff(c_761,plain,(
    ! [C_123] :
      ( r1_tarski(k1_tops_2('#skF_1','#skF_2',C_123),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_742])).

tff(c_878,plain,(
    ! [C_134] :
      ( r1_tarski(k1_tops_2('#skF_1','#skF_2',C_134),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_761])).

tff(c_887,plain,(
    r1_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_878])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [A_60,B_61] :
      ( k5_setfam_1(A_60,B_61) = k3_tarski(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_131,plain,(
    ! [A_60,A_16] :
      ( k5_setfam_1(A_60,A_16) = k3_tarski(A_16)
      | ~ r1_tarski(A_16,k1_zfmisc_1(A_60)) ) ),
    inference(resolution,[status(thm)],[c_22,c_123])).

tff(c_906,plain,(
    k5_setfam_1('#skF_2',k1_tops_2('#skF_1','#skF_2','#skF_3')) = k3_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_887,c_131])).

tff(c_30,plain,(
    k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_233,plain,(
    k5_setfam_1('#skF_2',k1_tops_2('#skF_1','#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_30])).

tff(c_926,plain,(
    k3_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_233])).

tff(c_132,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_123])).

tff(c_32,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_134,plain,(
    r1_tarski('#skF_2',k3_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_32])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_148,plain,(
    ! [B_63] : k9_subset_1(u1_struct_0('#skF_1'),B_63,'#skF_2') = k3_xboole_0(B_63,'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_600,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( r1_tarski(k9_subset_1(u1_struct_0(A_105),B_106,C_107),k5_setfam_1(u1_struct_0(k1_pre_topc(A_105,C_107)),k1_tops_2(A_105,C_107,D_108)))
      | ~ r1_tarski(B_106,k5_setfam_1(u1_struct_0(A_105),D_108))
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105))))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_634,plain,(
    ! [B_63,D_108] :
      ( r1_tarski(k3_xboole_0(B_63,'#skF_2'),k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2',D_108)))
      | ~ r1_tarski(B_63,k5_setfam_1(u1_struct_0('#skF_1'),D_108))
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_600])).

tff(c_646,plain,(
    ! [B_63,D_108] :
      ( r1_tarski(k3_xboole_0(B_63,'#skF_2'),k5_setfam_1('#skF_2',k1_tops_2('#skF_1','#skF_2',D_108)))
      | ~ r1_tarski(B_63,k5_setfam_1(u1_struct_0('#skF_1'),D_108))
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_232,c_634])).

tff(c_930,plain,(
    ! [B_63] :
      ( r1_tarski(k3_xboole_0(B_63,'#skF_2'),k3_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3')))
      | ~ r1_tarski(B_63,k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_646])).

tff(c_2790,plain,(
    ! [B_292] :
      ( r1_tarski(k3_xboole_0(B_292,'#skF_2'),k3_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3')))
      | ~ r1_tarski(B_292,k3_tarski('#skF_3'))
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_132,c_930])).

tff(c_2826,plain,
    ( r1_tarski('#skF_2',k3_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3')))
    | ~ r1_tarski('#skF_2',k3_tarski('#skF_3'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2790])).

tff(c_2840,plain,(
    r1_tarski('#skF_2',k3_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_134,c_2826])).

tff(c_12,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k3_tarski(A_52),k3_tarski(B_53))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [A_56,A_57] :
      ( r1_tarski(k3_tarski(A_56),A_57)
      | ~ r1_tarski(A_56,k1_zfmisc_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_90])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_56,A_57] :
      ( k3_tarski(A_56) = A_57
      | ~ r1_tarski(A_57,k3_tarski(A_56))
      | ~ r1_tarski(A_56,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_2856,plain,
    ( k3_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2840,c_113])).

tff(c_2876,plain,(
    k3_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_2856])).

tff(c_2878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_926,c_2876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:34:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/1.96  
% 5.35/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/1.96  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k5_setfam_1 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.35/1.96  
% 5.35/1.96  %Foreground sorts:
% 5.35/1.96  
% 5.35/1.96  
% 5.35/1.96  %Background operators:
% 5.35/1.96  
% 5.35/1.96  
% 5.35/1.96  %Foreground operators:
% 5.35/1.96  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 5.35/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.35/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.35/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.35/1.96  tff('#skF_1', type, '#skF_1': $i).
% 5.35/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/1.96  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 5.35/1.96  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 5.35/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/1.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.35/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.35/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.35/1.96  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.35/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/1.96  
% 5.35/1.98  tff(f_98, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(A), C)) => (B = k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_2)).
% 5.35/1.98  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 5.35/1.98  tff(f_70, axiom, (![A, B, C]: (((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) => m1_subset_1(k1_tops_2(A, B, C), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 5.35/1.98  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.35/1.98  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 5.35/1.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.35/1.98  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.35/1.98  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(A), D)) => r1_tarski(k9_subset_1(u1_struct_0(A), B, C), k5_setfam_1(u1_struct_0(k1_pre_topc(A, C)), k1_tops_2(A, C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tops_2)).
% 5.35/1.98  tff(f_39, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.35/1.98  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 5.35/1.98  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.35/1.98  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.35/1.98  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.35/1.98  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.35/1.98  tff(c_221, plain, (![A_73, B_74]: (u1_struct_0(k1_pre_topc(A_73, B_74))=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.35/1.98  tff(c_228, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_221])).
% 5.35/1.98  tff(c_232, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_228])).
% 5.35/1.98  tff(c_479, plain, (![A_95, B_96, C_97]: (m1_subset_1(k1_tops_2(A_95, B_96, C_97), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_95, B_96))))) | ~m1_subset_1(C_97, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95)))) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.35/1.98  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.35/1.98  tff(c_742, plain, (![A_121, B_122, C_123]: (r1_tarski(k1_tops_2(A_121, B_122, C_123), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_121, B_122)))) | ~m1_subset_1(C_123, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_121)))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_479, c_20])).
% 5.35/1.98  tff(c_761, plain, (![C_123]: (r1_tarski(k1_tops_2('#skF_1', '#skF_2', C_123), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(C_123, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_232, c_742])).
% 5.35/1.98  tff(c_878, plain, (![C_134]: (r1_tarski(k1_tops_2('#skF_1', '#skF_2', C_134), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(C_134, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_761])).
% 5.35/1.98  tff(c_887, plain, (r1_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_878])).
% 5.35/1.98  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.35/1.98  tff(c_123, plain, (![A_60, B_61]: (k5_setfam_1(A_60, B_61)=k3_tarski(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.35/1.98  tff(c_131, plain, (![A_60, A_16]: (k5_setfam_1(A_60, A_16)=k3_tarski(A_16) | ~r1_tarski(A_16, k1_zfmisc_1(A_60)))), inference(resolution, [status(thm)], [c_22, c_123])).
% 5.35/1.98  tff(c_906, plain, (k5_setfam_1('#skF_2', k1_tops_2('#skF_1', '#skF_2', '#skF_3'))=k3_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_887, c_131])).
% 5.35/1.98  tff(c_30, plain, (k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.35/1.98  tff(c_233, plain, (k5_setfam_1('#skF_2', k1_tops_2('#skF_1', '#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_30])).
% 5.35/1.98  tff(c_926, plain, (k3_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_906, c_233])).
% 5.35/1.98  tff(c_132, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_34, c_123])).
% 5.35/1.98  tff(c_32, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.35/1.98  tff(c_134, plain, (r1_tarski('#skF_2', k3_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_32])).
% 5.35/1.98  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.35/1.98  tff(c_139, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.35/1.98  tff(c_148, plain, (![B_63]: (k9_subset_1(u1_struct_0('#skF_1'), B_63, '#skF_2')=k3_xboole_0(B_63, '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_139])).
% 5.35/1.98  tff(c_600, plain, (![A_105, B_106, C_107, D_108]: (r1_tarski(k9_subset_1(u1_struct_0(A_105), B_106, C_107), k5_setfam_1(u1_struct_0(k1_pre_topc(A_105, C_107)), k1_tops_2(A_105, C_107, D_108))) | ~r1_tarski(B_106, k5_setfam_1(u1_struct_0(A_105), D_108)) | ~m1_subset_1(D_108, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105)))) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.35/1.98  tff(c_634, plain, (![B_63, D_108]: (r1_tarski(k3_xboole_0(B_63, '#skF_2'), k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', D_108))) | ~r1_tarski(B_63, k5_setfam_1(u1_struct_0('#skF_1'), D_108)) | ~m1_subset_1(D_108, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_600])).
% 5.35/1.98  tff(c_646, plain, (![B_63, D_108]: (r1_tarski(k3_xboole_0(B_63, '#skF_2'), k5_setfam_1('#skF_2', k1_tops_2('#skF_1', '#skF_2', D_108))) | ~r1_tarski(B_63, k5_setfam_1(u1_struct_0('#skF_1'), D_108)) | ~m1_subset_1(D_108, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_232, c_634])).
% 5.35/1.98  tff(c_930, plain, (![B_63]: (r1_tarski(k3_xboole_0(B_63, '#skF_2'), k3_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'))) | ~r1_tarski(B_63, k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_906, c_646])).
% 5.35/1.98  tff(c_2790, plain, (![B_292]: (r1_tarski(k3_xboole_0(B_292, '#skF_2'), k3_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'))) | ~r1_tarski(B_292, k3_tarski('#skF_3')) | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_132, c_930])).
% 5.35/1.98  tff(c_2826, plain, (r1_tarski('#skF_2', k3_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'))) | ~r1_tarski('#skF_2', k3_tarski('#skF_3')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2790])).
% 5.35/1.98  tff(c_2840, plain, (r1_tarski('#skF_2', k3_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_134, c_2826])).
% 5.35/1.98  tff(c_12, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.35/1.98  tff(c_90, plain, (![A_52, B_53]: (r1_tarski(k3_tarski(A_52), k3_tarski(B_53)) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.35/1.98  tff(c_107, plain, (![A_56, A_57]: (r1_tarski(k3_tarski(A_56), A_57) | ~r1_tarski(A_56, k1_zfmisc_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_90])).
% 5.35/1.98  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.35/1.98  tff(c_113, plain, (![A_56, A_57]: (k3_tarski(A_56)=A_57 | ~r1_tarski(A_57, k3_tarski(A_56)) | ~r1_tarski(A_56, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_107, c_4])).
% 5.35/1.98  tff(c_2856, plain, (k3_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_2840, c_113])).
% 5.35/1.98  tff(c_2876, plain, (k3_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_887, c_2856])).
% 5.35/1.98  tff(c_2878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_926, c_2876])).
% 5.35/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/1.98  
% 5.35/1.98  Inference rules
% 5.35/1.98  ----------------------
% 5.35/1.98  #Ref     : 0
% 5.35/1.98  #Sup     : 648
% 5.35/1.98  #Fact    : 0
% 5.35/1.98  #Define  : 0
% 5.35/1.98  #Split   : 9
% 5.35/1.98  #Chain   : 0
% 5.35/1.98  #Close   : 0
% 5.35/1.98  
% 5.35/1.98  Ordering : KBO
% 5.35/1.98  
% 5.35/1.98  Simplification rules
% 5.35/1.98  ----------------------
% 5.35/1.98  #Subsume      : 98
% 5.35/1.98  #Demod        : 426
% 5.35/1.98  #Tautology    : 263
% 5.35/1.98  #SimpNegUnit  : 2
% 5.35/1.98  #BackRed      : 4
% 5.35/1.98  
% 5.35/1.98  #Partial instantiations: 0
% 5.35/1.98  #Strategies tried      : 1
% 5.35/1.98  
% 5.35/1.98  Timing (in seconds)
% 5.35/1.98  ----------------------
% 5.35/1.98  Preprocessing        : 0.31
% 5.35/1.98  Parsing              : 0.17
% 5.35/1.98  CNF conversion       : 0.02
% 5.35/1.98  Main loop            : 0.91
% 5.35/1.98  Inferencing          : 0.29
% 5.35/1.98  Reduction            : 0.29
% 5.35/1.98  Demodulation         : 0.21
% 5.35/1.98  BG Simplification    : 0.04
% 5.35/1.98  Subsumption          : 0.24
% 5.50/1.98  Abstraction          : 0.05
% 5.50/1.98  MUC search           : 0.00
% 5.50/1.98  Cooper               : 0.00
% 5.50/1.98  Total                : 1.25
% 5.50/1.98  Index Insertion      : 0.00
% 5.50/1.98  Index Deletion       : 0.00
% 5.50/1.98  Index Matching       : 0.00
% 5.50/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
