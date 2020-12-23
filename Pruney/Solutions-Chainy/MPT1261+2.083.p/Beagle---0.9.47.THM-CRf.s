%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:23 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 141 expanded)
%              Number of leaves         :   35 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 269 expanded)
%              Number of equality atoms :   55 (  97 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_70,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2334,plain,(
    ! [A_160,B_161,C_162] :
      ( k7_subset_1(A_160,B_161,C_162) = k4_xboole_0(B_161,C_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2337,plain,(
    ! [C_162] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_162) = k4_xboole_0('#skF_2',C_162) ),
    inference(resolution,[status(thm)],[c_30,c_2334])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_282,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_930,plain,(
    ! [B_91,A_92] :
      ( v4_pre_topc(B_91,A_92)
      | k2_pre_topc(A_92,B_91) != B_91
      | ~ v2_pre_topc(A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_936,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_930])).

tff(c_940,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_936])).

tff(c_941,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_940])).

tff(c_976,plain,(
    ! [A_96,B_97] :
      ( k4_subset_1(u1_struct_0(A_96),B_97,k2_tops_1(A_96,B_97)) = k2_pre_topc(A_96,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_980,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_976])).

tff(c_984,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_980])).

tff(c_410,plain,(
    ! [A_63,B_64,C_65] :
      ( k7_subset_1(A_63,B_64,C_65) = k4_xboole_0(B_64,C_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_414,plain,(
    ! [C_66] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_66) = k4_xboole_0('#skF_2',C_66) ),
    inference(resolution,[status(thm)],[c_30,c_410])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_162,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_420,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_162])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_163,plain,(
    ! [B_43,A_44] : k3_tarski(k2_tarski(B_43,A_44)) = k2_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_91])).

tff(c_12,plain,(
    ! [A_11,B_12] : k3_tarski(k2_tarski(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_12])).

tff(c_245,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_254,plain,(
    ! [A_51,B_52] : k2_xboole_0(k4_xboole_0(A_51,B_52),k3_xboole_0(A_51,B_52)) = k2_xboole_0(k4_xboole_0(A_51,B_52),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_4])).

tff(c_839,plain,(
    ! [A_87,B_88] : k2_xboole_0(k4_xboole_0(A_87,B_88),k3_xboole_0(A_87,B_88)) = k2_xboole_0(A_87,k4_xboole_0(A_87,B_88)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_254])).

tff(c_845,plain,(
    ! [A_87,B_88] : k2_xboole_0(k3_xboole_0(A_87,B_88),k4_xboole_0(A_87,B_88)) = k2_xboole_0(A_87,k4_xboole_0(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_169])).

tff(c_895,plain,(
    ! [A_89,B_90] : k2_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_845])).

tff(c_917,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_895])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_715,plain,(
    ! [A_79,B_80,C_81] :
      ( k4_subset_1(A_79,B_80,C_81) = k2_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1876,plain,(
    ! [A_128,B_129,B_130] :
      ( k4_subset_1(u1_struct_0(A_128),B_129,k2_tops_1(A_128,B_130)) = k2_xboole_0(B_129,k2_tops_1(A_128,B_130))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_24,c_715])).

tff(c_1880,plain,(
    ! [B_130] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_130)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_130))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1876])).

tff(c_2043,plain,(
    ! [B_137] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_137)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_137))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1880])).

tff(c_2050,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_2043])).

tff(c_2055,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_917,c_2050])).

tff(c_2057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_941,c_2055])).

tff(c_2058,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2058,c_162])).

tff(c_2121,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2147,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_36])).

tff(c_2338,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_2147])).

tff(c_2381,plain,(
    ! [A_166,B_167] :
      ( k2_pre_topc(A_166,B_167) = B_167
      | ~ v4_pre_topc(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2384,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2381])).

tff(c_2387,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2121,c_2384])).

tff(c_2766,plain,(
    ! [A_197,B_198] :
      ( k7_subset_1(u1_struct_0(A_197),k2_pre_topc(A_197,B_198),k1_tops_1(A_197,B_198)) = k2_tops_1(A_197,B_198)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2775,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2387,c_2766])).

tff(c_2779,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2337,c_2775])).

tff(c_2781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2338,c_2779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.75  
% 4.16/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.76  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.16/1.76  
% 4.16/1.76  %Foreground sorts:
% 4.16/1.76  
% 4.16/1.76  
% 4.16/1.76  %Background operators:
% 4.16/1.76  
% 4.16/1.76  
% 4.16/1.76  %Foreground operators:
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.16/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.16/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.16/1.76  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.16/1.76  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.16/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.76  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.16/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.16/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.76  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.16/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.16/1.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.16/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.16/1.76  
% 4.16/1.77  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.16/1.77  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.16/1.77  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.16/1.77  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.16/1.77  tff(f_33, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.16/1.77  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.16/1.77  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.16/1.77  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.16/1.77  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.16/1.77  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.16/1.77  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.16/1.77  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.16/1.77  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.16/1.77  tff(c_2334, plain, (![A_160, B_161, C_162]: (k7_subset_1(A_160, B_161, C_162)=k4_xboole_0(B_161, C_162) | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.16/1.77  tff(c_2337, plain, (![C_162]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_162)=k4_xboole_0('#skF_2', C_162))), inference(resolution, [status(thm)], [c_30, c_2334])).
% 4.16/1.77  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.16/1.77  tff(c_282, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 4.16/1.77  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.16/1.77  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.16/1.77  tff(c_930, plain, (![B_91, A_92]: (v4_pre_topc(B_91, A_92) | k2_pre_topc(A_92, B_91)!=B_91 | ~v2_pre_topc(A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.16/1.77  tff(c_936, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_930])).
% 4.16/1.77  tff(c_940, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_936])).
% 4.16/1.77  tff(c_941, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_282, c_940])).
% 4.16/1.77  tff(c_976, plain, (![A_96, B_97]: (k4_subset_1(u1_struct_0(A_96), B_97, k2_tops_1(A_96, B_97))=k2_pre_topc(A_96, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.16/1.77  tff(c_980, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_976])).
% 4.16/1.77  tff(c_984, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_980])).
% 4.16/1.77  tff(c_410, plain, (![A_63, B_64, C_65]: (k7_subset_1(A_63, B_64, C_65)=k4_xboole_0(B_64, C_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.16/1.77  tff(c_414, plain, (![C_66]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_66)=k4_xboole_0('#skF_2', C_66))), inference(resolution, [status(thm)], [c_30, c_410])).
% 4.16/1.77  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.16/1.77  tff(c_162, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 4.16/1.77  tff(c_420, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_414, c_162])).
% 4.16/1.77  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.77  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.16/1.77  tff(c_91, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.77  tff(c_163, plain, (![B_43, A_44]: (k3_tarski(k2_tarski(B_43, A_44))=k2_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_10, c_91])).
% 4.16/1.77  tff(c_12, plain, (![A_11, B_12]: (k3_tarski(k2_tarski(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.77  tff(c_169, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_163, c_12])).
% 4.16/1.77  tff(c_245, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.77  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.16/1.77  tff(c_254, plain, (![A_51, B_52]: (k2_xboole_0(k4_xboole_0(A_51, B_52), k3_xboole_0(A_51, B_52))=k2_xboole_0(k4_xboole_0(A_51, B_52), A_51))), inference(superposition, [status(thm), theory('equality')], [c_245, c_4])).
% 4.16/1.77  tff(c_839, plain, (![A_87, B_88]: (k2_xboole_0(k4_xboole_0(A_87, B_88), k3_xboole_0(A_87, B_88))=k2_xboole_0(A_87, k4_xboole_0(A_87, B_88)))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_254])).
% 4.16/1.77  tff(c_845, plain, (![A_87, B_88]: (k2_xboole_0(k3_xboole_0(A_87, B_88), k4_xboole_0(A_87, B_88))=k2_xboole_0(A_87, k4_xboole_0(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_839, c_169])).
% 4.16/1.77  tff(c_895, plain, (![A_89, B_90]: (k2_xboole_0(A_89, k4_xboole_0(A_89, B_90))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_845])).
% 4.16/1.77  tff(c_917, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_420, c_895])).
% 4.16/1.77  tff(c_24, plain, (![A_24, B_25]: (m1_subset_1(k2_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.16/1.77  tff(c_715, plain, (![A_79, B_80, C_81]: (k4_subset_1(A_79, B_80, C_81)=k2_xboole_0(B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.16/1.77  tff(c_1876, plain, (![A_128, B_129, B_130]: (k4_subset_1(u1_struct_0(A_128), B_129, k2_tops_1(A_128, B_130))=k2_xboole_0(B_129, k2_tops_1(A_128, B_130)) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_24, c_715])).
% 4.16/1.77  tff(c_1880, plain, (![B_130]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_130))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_130)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1876])).
% 4.16/1.77  tff(c_2043, plain, (![B_137]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_137))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_137)) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1880])).
% 4.16/1.77  tff(c_2050, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_2043])).
% 4.16/1.77  tff(c_2055, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_984, c_917, c_2050])).
% 4.16/1.77  tff(c_2057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_941, c_2055])).
% 4.16/1.77  tff(c_2058, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 4.16/1.77  tff(c_2120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2058, c_162])).
% 4.16/1.77  tff(c_2121, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.16/1.77  tff(c_2147, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_36])).
% 4.16/1.77  tff(c_2338, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_2147])).
% 4.16/1.77  tff(c_2381, plain, (![A_166, B_167]: (k2_pre_topc(A_166, B_167)=B_167 | ~v4_pre_topc(B_167, A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.16/1.77  tff(c_2384, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2381])).
% 4.16/1.77  tff(c_2387, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2121, c_2384])).
% 4.16/1.77  tff(c_2766, plain, (![A_197, B_198]: (k7_subset_1(u1_struct_0(A_197), k2_pre_topc(A_197, B_198), k1_tops_1(A_197, B_198))=k2_tops_1(A_197, B_198) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.16/1.77  tff(c_2775, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2387, c_2766])).
% 4.16/1.77  tff(c_2779, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2337, c_2775])).
% 4.16/1.77  tff(c_2781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2338, c_2779])).
% 4.16/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.77  
% 4.16/1.77  Inference rules
% 4.16/1.77  ----------------------
% 4.16/1.77  #Ref     : 0
% 4.16/1.77  #Sup     : 696
% 4.16/1.77  #Fact    : 0
% 4.16/1.77  #Define  : 0
% 4.16/1.77  #Split   : 3
% 4.16/1.77  #Chain   : 0
% 4.16/1.77  #Close   : 0
% 4.16/1.77  
% 4.16/1.77  Ordering : KBO
% 4.16/1.77  
% 4.16/1.77  Simplification rules
% 4.16/1.77  ----------------------
% 4.16/1.77  #Subsume      : 18
% 4.16/1.77  #Demod        : 390
% 4.16/1.77  #Tautology    : 409
% 4.16/1.77  #SimpNegUnit  : 4
% 4.16/1.77  #BackRed      : 5
% 4.16/1.77  
% 4.16/1.77  #Partial instantiations: 0
% 4.16/1.77  #Strategies tried      : 1
% 4.16/1.77  
% 4.16/1.77  Timing (in seconds)
% 4.16/1.77  ----------------------
% 4.45/1.78  Preprocessing        : 0.32
% 4.45/1.78  Parsing              : 0.17
% 4.45/1.78  CNF conversion       : 0.02
% 4.45/1.78  Main loop            : 0.70
% 4.45/1.78  Inferencing          : 0.22
% 4.45/1.78  Reduction            : 0.31
% 4.45/1.78  Demodulation         : 0.26
% 4.45/1.78  BG Simplification    : 0.03
% 4.45/1.78  Subsumption          : 0.10
% 4.45/1.78  Abstraction          : 0.04
% 4.45/1.78  MUC search           : 0.00
% 4.45/1.78  Cooper               : 0.00
% 4.45/1.78  Total                : 1.05
% 4.45/1.78  Index Insertion      : 0.00
% 4.45/1.78  Index Deletion       : 0.00
% 4.45/1.78  Index Matching       : 0.00
% 4.45/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
