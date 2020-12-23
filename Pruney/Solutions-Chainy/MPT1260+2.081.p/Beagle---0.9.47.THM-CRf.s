%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:11 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 330 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :   14
%              Number of atoms          :  202 ( 753 expanded)
%              Number of equality atoms :   61 ( 174 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_289,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(B_89,k2_pre_topc(A_90,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_297,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_289])).

tff(c_305,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_297])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_77,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_221,plain,(
    ! [A_81,B_82,C_83] :
      ( k7_subset_1(A_81,B_82,C_83) = k4_xboole_0(B_82,C_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_603,plain,(
    ! [A_119,B_120,C_121] :
      ( k7_subset_1(A_119,k3_subset_1(A_119,B_120),C_121) = k4_xboole_0(k3_subset_1(A_119,B_120),C_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_6,c_221])).

tff(c_618,plain,(
    ! [C_121] : k7_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),C_121) = k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),C_121) ),
    inference(resolution,[status(thm)],[c_38,c_603])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1('#skF_1'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,B_65) = B_65
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,(
    ! [A_64,B_65] : k9_subset_1(A_64,B_65,B_65) = B_65 ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_461,plain,(
    ! [A_111,B_112,C_113] :
      ( k9_subset_1(A_111,B_112,k3_subset_1(A_111,C_113)) = k7_subset_1(A_111,B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_696,plain,(
    ! [B_130] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_130,k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(u1_struct_0('#skF_2'),B_130,'#skF_3')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_461])).

tff(c_710,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_696])).

tff(c_714,plain,
    ( k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_710])).

tff(c_876,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_879,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_876])).

tff(c_886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_879])).

tff(c_888,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_32,plain,(
    ! [C_47,A_35,D_49,B_43] :
      ( v3_pre_topc(C_47,A_35)
      | k1_tops_1(A_35,C_47) != C_47
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0(B_43)))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(B_43)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_964,plain,(
    ! [D_146,B_147] :
      ( ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(B_147)))
      | ~ l1_pre_topc(B_147) ) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_967,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_888,c_964])).

tff(c_985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_967])).

tff(c_994,plain,(
    ! [C_148,A_149] :
      ( v3_pre_topc(C_148,A_149)
      | k1_tops_1(A_149,C_148) != C_148
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149) ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1011,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_994])).

tff(c_1024,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1011])).

tff(c_1025,plain,(
    k1_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_1024])).

tff(c_337,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1(k2_pre_topc(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( k7_subset_1(A_14,B_15,C_16) = k4_xboole_0(B_15,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2263,plain,(
    ! [A_196,B_197,C_198] :
      ( k7_subset_1(u1_struct_0(A_196),k2_pre_topc(A_196,B_197),C_198) = k4_xboole_0(k2_pre_topc(A_196,B_197),C_198)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_337,c_14])).

tff(c_2275,plain,(
    ! [C_198] :
      ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_198) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_198)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_2263])).

tff(c_2289,plain,(
    ! [C_199] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_199) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2275])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_133,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_50])).

tff(c_2311,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_133])).

tff(c_115,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = k3_subset_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [B_24,A_23] :
      ( k4_xboole_0(B_24,A_23) = k3_subset_1(B_24,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_22,c_115])).

tff(c_313,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_305,c_130])).

tff(c_2344,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_313])).

tff(c_156,plain,(
    ! [A_77,B_78] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,B_78)) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_167,plain,(
    ! [B_24,A_23] :
      ( k3_subset_1(B_24,k3_subset_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_22,c_156])).

tff(c_2383,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2344,c_167])).

tff(c_2411,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_2383])).

tff(c_233,plain,(
    ! [C_83] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_83) = k4_xboole_0('#skF_3',C_83) ),
    inference(resolution,[status(thm)],[c_38,c_221])).

tff(c_412,plain,(
    ! [A_107,B_108] :
      ( k7_subset_1(u1_struct_0(A_107),B_108,k2_tops_1(A_107,B_108)) = k1_tops_1(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_422,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_412])).

tff(c_431,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_233,c_422])).

tff(c_232,plain,(
    ! [B_24,A_23,C_83] :
      ( k7_subset_1(B_24,A_23,C_83) = k4_xboole_0(A_23,C_83)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_22,c_221])).

tff(c_312,plain,(
    ! [C_83] : k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',C_83) = k4_xboole_0('#skF_3',C_83) ),
    inference(resolution,[status(thm)],[c_305,c_232])).

tff(c_108,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k3_subset_1(A_69,B_70),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k3_subset_1(A_69,B_70),A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_108,c_20])).

tff(c_1079,plain,(
    ! [B_154,B_155,A_156] :
      ( k9_subset_1(B_154,B_155,k3_subset_1(B_154,A_156)) = k7_subset_1(B_154,B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(B_154))
      | ~ r1_tarski(A_156,B_154) ) ),
    inference(resolution,[status(thm)],[c_22,c_461])).

tff(c_1144,plain,(
    ! [B_158,A_159,A_160] :
      ( k9_subset_1(B_158,A_159,k3_subset_1(B_158,A_160)) = k7_subset_1(B_158,A_159,A_160)
      | ~ r1_tarski(A_160,B_158)
      | ~ r1_tarski(A_159,B_158) ) ),
    inference(resolution,[status(thm)],[c_22,c_1079])).

tff(c_1387,plain,(
    ! [A_168,A_169] :
      ( k7_subset_1(A_168,k3_subset_1(A_168,A_169),A_169) = k3_subset_1(A_168,A_169)
      | ~ r1_tarski(A_169,A_168)
      | ~ r1_tarski(k3_subset_1(A_168,A_169),A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1144])).

tff(c_1408,plain,(
    ! [A_170,B_171] :
      ( k7_subset_1(A_170,k3_subset_1(A_170,B_171),B_171) = k3_subset_1(A_170,B_171)
      | ~ r1_tarski(B_171,A_170)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(A_170)) ) ),
    inference(resolution,[status(thm)],[c_112,c_1387])).

tff(c_1427,plain,(
    ! [B_24,A_23] :
      ( k7_subset_1(B_24,k3_subset_1(B_24,A_23),A_23) = k3_subset_1(B_24,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_22,c_1408])).

tff(c_2428,plain,
    ( k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2411,c_1427])).

tff(c_2461,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2411,c_431,c_312,c_2428])).

tff(c_2462,plain,(
    ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),k2_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1025,c_2461])).

tff(c_2386,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2344,c_112])).

tff(c_2483,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2462,c_2386])).

tff(c_2486,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_2483])).

tff(c_2490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_2486])).

tff(c_2491,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2492,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_34,plain,(
    ! [B_43,D_49,C_47,A_35] :
      ( k1_tops_1(B_43,D_49) = D_49
      | ~ v3_pre_topc(D_49,B_43)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0(B_43)))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(B_43)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3189,plain,(
    ! [C_275,A_276] :
      ( ~ m1_subset_1(C_275,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276) ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_3203,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_3189])).

tff(c_3213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3203])).

tff(c_3215,plain,(
    ! [B_277,D_278] :
      ( k1_tops_1(B_277,D_278) = D_278
      | ~ v3_pre_topc(D_278,B_277)
      | ~ m1_subset_1(D_278,k1_zfmisc_1(u1_struct_0(B_277)))
      | ~ l1_pre_topc(B_277) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3229,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_3215])).

tff(c_3239,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2492,c_3229])).

tff(c_30,plain,(
    ! [A_32,B_34] :
      ( k7_subset_1(u1_struct_0(A_32),k2_pre_topc(A_32,B_34),k1_tops_1(A_32,B_34)) = k2_tops_1(A_32,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3247,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3239,c_30])).

tff(c_3254,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3247])).

tff(c_3256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2491,c_3254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:48:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.93  
% 4.78/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.93  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 4.96/1.93  
% 4.96/1.93  %Foreground sorts:
% 4.96/1.93  
% 4.96/1.93  
% 4.96/1.93  %Background operators:
% 4.96/1.93  
% 4.96/1.93  
% 4.96/1.93  %Foreground operators:
% 4.96/1.93  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.96/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.96/1.93  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.96/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.96/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.96/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.96/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.96/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.96/1.93  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.96/1.93  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.96/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.96/1.93  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.96/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.96/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.96/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.96/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.96/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.96/1.93  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.96/1.93  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.96/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.96/1.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.96/1.93  
% 5.02/1.95  tff(f_131, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 5.02/1.95  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 5.02/1.95  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.02/1.95  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.02/1.95  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.02/1.95  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.02/1.95  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 5.02/1.95  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 5.02/1.95  tff(f_112, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 5.02/1.95  tff(f_69, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.02/1.95  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.02/1.95  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.02/1.95  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 5.02/1.95  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.02/1.95  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.02/1.95  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.02/1.95  tff(c_289, plain, (![B_89, A_90]: (r1_tarski(B_89, k2_pre_topc(A_90, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.02/1.95  tff(c_297, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_289])).
% 5.02/1.95  tff(c_305, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_297])).
% 5.02/1.95  tff(c_22, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.02/1.95  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.02/1.95  tff(c_77, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 5.02/1.95  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.02/1.95  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.02/1.95  tff(c_221, plain, (![A_81, B_82, C_83]: (k7_subset_1(A_81, B_82, C_83)=k4_xboole_0(B_82, C_83) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.02/1.95  tff(c_603, plain, (![A_119, B_120, C_121]: (k7_subset_1(A_119, k3_subset_1(A_119, B_120), C_121)=k4_xboole_0(k3_subset_1(A_119, B_120), C_121) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(resolution, [status(thm)], [c_6, c_221])).
% 5.02/1.95  tff(c_618, plain, (![C_121]: (k7_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), C_121)=k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), C_121))), inference(resolution, [status(thm)], [c_38, c_603])).
% 5.02/1.95  tff(c_8, plain, (![A_7]: (m1_subset_1('#skF_1'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.02/1.95  tff(c_87, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, B_65)=B_65 | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.02/1.95  tff(c_96, plain, (![A_64, B_65]: (k9_subset_1(A_64, B_65, B_65)=B_65)), inference(resolution, [status(thm)], [c_8, c_87])).
% 5.02/1.95  tff(c_461, plain, (![A_111, B_112, C_113]: (k9_subset_1(A_111, B_112, k3_subset_1(A_111, C_113))=k7_subset_1(A_111, B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.95  tff(c_696, plain, (![B_130]: (k9_subset_1(u1_struct_0('#skF_2'), B_130, k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(u1_struct_0('#skF_2'), B_130, '#skF_3') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_461])).
% 5.02/1.95  tff(c_710, plain, (k7_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_696])).
% 5.02/1.95  tff(c_714, plain, (k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_710])).
% 5.02/1.95  tff(c_876, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_714])).
% 5.02/1.95  tff(c_879, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_876])).
% 5.02/1.95  tff(c_886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_879])).
% 5.02/1.95  tff(c_888, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_714])).
% 5.02/1.95  tff(c_32, plain, (![C_47, A_35, D_49, B_43]: (v3_pre_topc(C_47, A_35) | k1_tops_1(A_35, C_47)!=C_47 | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0(B_43))) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(B_43) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.02/1.95  tff(c_964, plain, (![D_146, B_147]: (~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(B_147))) | ~l1_pre_topc(B_147))), inference(splitLeft, [status(thm)], [c_32])).
% 5.02/1.95  tff(c_967, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_888, c_964])).
% 5.02/1.95  tff(c_985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_967])).
% 5.02/1.95  tff(c_994, plain, (![C_148, A_149]: (v3_pre_topc(C_148, A_149) | k1_tops_1(A_149, C_148)!=C_148 | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149))), inference(splitRight, [status(thm)], [c_32])).
% 5.02/1.95  tff(c_1011, plain, (v3_pre_topc('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_994])).
% 5.02/1.95  tff(c_1024, plain, (v3_pre_topc('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1011])).
% 5.02/1.95  tff(c_1025, plain, (k1_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_77, c_1024])).
% 5.02/1.95  tff(c_337, plain, (![A_93, B_94]: (m1_subset_1(k2_pre_topc(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.02/1.95  tff(c_14, plain, (![A_14, B_15, C_16]: (k7_subset_1(A_14, B_15, C_16)=k4_xboole_0(B_15, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.02/1.95  tff(c_2263, plain, (![A_196, B_197, C_198]: (k7_subset_1(u1_struct_0(A_196), k2_pre_topc(A_196, B_197), C_198)=k4_xboole_0(k2_pre_topc(A_196, B_197), C_198) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196))), inference(resolution, [status(thm)], [c_337, c_14])).
% 5.02/1.95  tff(c_2275, plain, (![C_198]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_198)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_198) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_2263])).
% 5.02/1.95  tff(c_2289, plain, (![C_199]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_199)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_199))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2275])).
% 5.02/1.95  tff(c_50, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.02/1.95  tff(c_133, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_77, c_50])).
% 5.02/1.95  tff(c_2311, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2289, c_133])).
% 5.02/1.95  tff(c_115, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=k3_subset_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.02/1.95  tff(c_130, plain, (![B_24, A_23]: (k4_xboole_0(B_24, A_23)=k3_subset_1(B_24, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_22, c_115])).
% 5.02/1.95  tff(c_313, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_305, c_130])).
% 5.02/1.95  tff(c_2344, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_313])).
% 5.02/1.95  tff(c_156, plain, (![A_77, B_78]: (k3_subset_1(A_77, k3_subset_1(A_77, B_78))=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.02/1.95  tff(c_167, plain, (![B_24, A_23]: (k3_subset_1(B_24, k3_subset_1(B_24, A_23))=A_23 | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_22, c_156])).
% 5.02/1.95  tff(c_2383, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2344, c_167])).
% 5.02/1.95  tff(c_2411, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_305, c_2383])).
% 5.02/1.95  tff(c_233, plain, (![C_83]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_83)=k4_xboole_0('#skF_3', C_83))), inference(resolution, [status(thm)], [c_38, c_221])).
% 5.02/1.95  tff(c_412, plain, (![A_107, B_108]: (k7_subset_1(u1_struct_0(A_107), B_108, k2_tops_1(A_107, B_108))=k1_tops_1(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.02/1.95  tff(c_422, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_412])).
% 5.02/1.95  tff(c_431, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_233, c_422])).
% 5.02/1.95  tff(c_232, plain, (![B_24, A_23, C_83]: (k7_subset_1(B_24, A_23, C_83)=k4_xboole_0(A_23, C_83) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_22, c_221])).
% 5.02/1.95  tff(c_312, plain, (![C_83]: (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', C_83)=k4_xboole_0('#skF_3', C_83))), inference(resolution, [status(thm)], [c_305, c_232])).
% 5.02/1.95  tff(c_108, plain, (![A_69, B_70]: (m1_subset_1(k3_subset_1(A_69, B_70), k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.02/1.95  tff(c_20, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.02/1.95  tff(c_112, plain, (![A_69, B_70]: (r1_tarski(k3_subset_1(A_69, B_70), A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_108, c_20])).
% 5.02/1.95  tff(c_1079, plain, (![B_154, B_155, A_156]: (k9_subset_1(B_154, B_155, k3_subset_1(B_154, A_156))=k7_subset_1(B_154, B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(B_154)) | ~r1_tarski(A_156, B_154))), inference(resolution, [status(thm)], [c_22, c_461])).
% 5.02/1.95  tff(c_1144, plain, (![B_158, A_159, A_160]: (k9_subset_1(B_158, A_159, k3_subset_1(B_158, A_160))=k7_subset_1(B_158, A_159, A_160) | ~r1_tarski(A_160, B_158) | ~r1_tarski(A_159, B_158))), inference(resolution, [status(thm)], [c_22, c_1079])).
% 5.02/1.95  tff(c_1387, plain, (![A_168, A_169]: (k7_subset_1(A_168, k3_subset_1(A_168, A_169), A_169)=k3_subset_1(A_168, A_169) | ~r1_tarski(A_169, A_168) | ~r1_tarski(k3_subset_1(A_168, A_169), A_168))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1144])).
% 5.02/1.95  tff(c_1408, plain, (![A_170, B_171]: (k7_subset_1(A_170, k3_subset_1(A_170, B_171), B_171)=k3_subset_1(A_170, B_171) | ~r1_tarski(B_171, A_170) | ~m1_subset_1(B_171, k1_zfmisc_1(A_170)))), inference(resolution, [status(thm)], [c_112, c_1387])).
% 5.02/1.95  tff(c_1427, plain, (![B_24, A_23]: (k7_subset_1(B_24, k3_subset_1(B_24, A_23), A_23)=k3_subset_1(B_24, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_22, c_1408])).
% 5.02/1.95  tff(c_2428, plain, (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2411, c_1427])).
% 5.02/1.95  tff(c_2461, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2411, c_431, c_312, c_2428])).
% 5.02/1.95  tff(c_2462, plain, (~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), k2_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1025, c_2461])).
% 5.02/1.95  tff(c_2386, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2344, c_112])).
% 5.02/1.95  tff(c_2483, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_2462, c_2386])).
% 5.02/1.95  tff(c_2486, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_2483])).
% 5.02/1.95  tff(c_2490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_305, c_2486])).
% 5.02/1.95  tff(c_2491, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 5.02/1.95  tff(c_2492, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.02/1.95  tff(c_34, plain, (![B_43, D_49, C_47, A_35]: (k1_tops_1(B_43, D_49)=D_49 | ~v3_pre_topc(D_49, B_43) | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0(B_43))) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(B_43) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.02/1.95  tff(c_3189, plain, (![C_275, A_276]: (~m1_subset_1(C_275, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276))), inference(splitLeft, [status(thm)], [c_34])).
% 5.02/1.95  tff(c_3203, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_3189])).
% 5.02/1.95  tff(c_3213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_3203])).
% 5.02/1.95  tff(c_3215, plain, (![B_277, D_278]: (k1_tops_1(B_277, D_278)=D_278 | ~v3_pre_topc(D_278, B_277) | ~m1_subset_1(D_278, k1_zfmisc_1(u1_struct_0(B_277))) | ~l1_pre_topc(B_277))), inference(splitRight, [status(thm)], [c_34])).
% 5.02/1.95  tff(c_3229, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_3215])).
% 5.02/1.95  tff(c_3239, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2492, c_3229])).
% 5.02/1.95  tff(c_30, plain, (![A_32, B_34]: (k7_subset_1(u1_struct_0(A_32), k2_pre_topc(A_32, B_34), k1_tops_1(A_32, B_34))=k2_tops_1(A_32, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.02/1.95  tff(c_3247, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3239, c_30])).
% 5.02/1.95  tff(c_3254, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3247])).
% 5.02/1.95  tff(c_3256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2491, c_3254])).
% 5.02/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.95  
% 5.02/1.95  Inference rules
% 5.02/1.95  ----------------------
% 5.02/1.95  #Ref     : 0
% 5.02/1.95  #Sup     : 755
% 5.02/1.95  #Fact    : 0
% 5.02/1.95  #Define  : 0
% 5.02/1.95  #Split   : 6
% 5.02/1.95  #Chain   : 0
% 5.02/1.95  #Close   : 0
% 5.02/1.95  
% 5.02/1.95  Ordering : KBO
% 5.02/1.95  
% 5.02/1.95  Simplification rules
% 5.02/1.95  ----------------------
% 5.02/1.95  #Subsume      : 67
% 5.02/1.95  #Demod        : 462
% 5.02/1.95  #Tautology    : 353
% 5.02/1.95  #SimpNegUnit  : 10
% 5.02/1.95  #BackRed      : 3
% 5.02/1.95  
% 5.02/1.95  #Partial instantiations: 0
% 5.02/1.95  #Strategies tried      : 1
% 5.02/1.95  
% 5.02/1.95  Timing (in seconds)
% 5.02/1.95  ----------------------
% 5.02/1.96  Preprocessing        : 0.36
% 5.02/1.96  Parsing              : 0.19
% 5.02/1.96  CNF conversion       : 0.02
% 5.02/1.96  Main loop            : 0.79
% 5.02/1.96  Inferencing          : 0.30
% 5.02/1.96  Reduction            : 0.26
% 5.02/1.96  Demodulation         : 0.19
% 5.02/1.96  BG Simplification    : 0.04
% 5.02/1.96  Subsumption          : 0.12
% 5.02/1.96  Abstraction          : 0.05
% 5.02/1.96  MUC search           : 0.00
% 5.02/1.96  Cooper               : 0.00
% 5.02/1.96  Total                : 1.18
% 5.02/1.96  Index Insertion      : 0.00
% 5.02/1.96  Index Deletion       : 0.00
% 5.02/1.96  Index Matching       : 0.00
% 5.02/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
