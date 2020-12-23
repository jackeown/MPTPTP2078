%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:15 EST 2020

% Result     : Theorem 10.32s
% Output     : CNFRefutation 10.32s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 213 expanded)
%              Number of leaves         :   29 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 495 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1623,plain,(
    ! [A_143,B_144] :
      ( k2_pre_topc(A_143,k1_tops_1(A_143,B_144)) = B_144
      | ~ v5_tops_1(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1632,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1623])).

tff(c_1638,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_1632])).

tff(c_38,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1639,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1638,c_38])).

tff(c_714,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k1_tops_1(A_94,B_95),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_721,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k1_tops_1(A_94,B_95),u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_714,c_20])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_368,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(B_70,k2_pre_topc(A_71,B_70))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_374,plain,(
    ! [A_18,A_71] :
      ( r1_tarski(A_18,k2_pre_topc(A_71,A_18))
      | ~ l1_pre_topc(A_71)
      | ~ r1_tarski(A_18,u1_struct_0(A_71)) ) ),
    inference(resolution,[status(thm)],[c_22,c_368])).

tff(c_1645,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_374])).

tff(c_1652,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1645])).

tff(c_1755,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1652])).

tff(c_1774,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_721,c_1755])).

tff(c_1778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1774])).

tff(c_1780,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1652])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k1_tops_1(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2013,plain,(
    ! [A_156,B_157] :
      ( k2_tops_1(A_156,k1_tops_1(A_156,B_157)) = k2_tops_1(A_156,B_157)
      | ~ v5_tops_1(B_157,A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2022,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2013])).

tff(c_2028,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_2022])).

tff(c_481,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k2_tops_1(A_76,B_77),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_488,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k2_tops_1(A_76,B_77),u1_struct_0(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_481,c_20])).

tff(c_2032,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2028,c_488])).

tff(c_2039,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2032])).

tff(c_4581,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2039])).

tff(c_4584,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4581])).

tff(c_4591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4584])).

tff(c_4592,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2039])).

tff(c_1936,plain,(
    ! [A_152,B_153] :
      ( k4_subset_1(u1_struct_0(A_152),B_153,k2_tops_1(A_152,B_153)) = k2_pre_topc(A_152,B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3193,plain,(
    ! [A_194,A_195] :
      ( k4_subset_1(u1_struct_0(A_194),A_195,k2_tops_1(A_194,A_195)) = k2_pre_topc(A_194,A_195)
      | ~ l1_pre_topc(A_194)
      | ~ r1_tarski(A_195,u1_struct_0(A_194)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1936])).

tff(c_3205,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2028,c_3193])).

tff(c_3215,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_44,c_1638,c_3205])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_tops_1(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1431,plain,(
    ! [A_131,C_132,B_133] :
      ( k4_subset_1(A_131,C_132,B_133) = k4_subset_1(A_131,B_133,C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(A_131))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5604,plain,(
    ! [A_274,B_275,B_276] :
      ( k4_subset_1(u1_struct_0(A_274),k2_tops_1(A_274,B_275),B_276) = k4_subset_1(u1_struct_0(A_274),B_276,k2_tops_1(A_274,B_275))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274) ) ),
    inference(resolution,[status(thm)],[c_32,c_1431])).

tff(c_17885,plain,(
    ! [A_480,B_481,A_482] :
      ( k4_subset_1(u1_struct_0(A_480),k2_tops_1(A_480,B_481),A_482) = k4_subset_1(u1_struct_0(A_480),A_482,k2_tops_1(A_480,B_481))
      | ~ m1_subset_1(B_481,k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ l1_pre_topc(A_480)
      | ~ r1_tarski(A_482,u1_struct_0(A_480)) ) ),
    inference(resolution,[status(thm)],[c_22,c_5604])).

tff(c_17898,plain,(
    ! [A_482] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),A_482) = k4_subset_1(u1_struct_0('#skF_1'),A_482,k2_tops_1('#skF_1','#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_482,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_17885])).

tff(c_17914,plain,(
    ! [A_483] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),A_483) = k4_subset_1(u1_struct_0('#skF_1'),A_483,k2_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_483,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_17898])).

tff(c_1259,plain,(
    ! [A_117,B_118,C_119] :
      ( k4_subset_1(A_117,B_118,C_119) = k2_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4915,plain,(
    ! [A_252,B_253,B_254] :
      ( k4_subset_1(u1_struct_0(A_252),B_253,k1_tops_1(A_252,B_254)) = k2_xboole_0(B_253,k1_tops_1(A_252,B_254))
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(resolution,[status(thm)],[c_30,c_1259])).

tff(c_13592,plain,(
    ! [A_434,A_435,B_436] :
      ( k4_subset_1(u1_struct_0(A_434),A_435,k1_tops_1(A_434,B_436)) = k2_xboole_0(A_435,k1_tops_1(A_434,B_436))
      | ~ m1_subset_1(B_436,k1_zfmisc_1(u1_struct_0(A_434)))
      | ~ l1_pre_topc(A_434)
      | ~ r1_tarski(A_435,u1_struct_0(A_434)) ) ),
    inference(resolution,[status(thm)],[c_22,c_4915])).

tff(c_13605,plain,(
    ! [A_435] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_435,k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(A_435,k1_tops_1('#skF_1','#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_435,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_13592])).

tff(c_13617,plain,(
    ! [A_435] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_435,k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(A_435,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_435,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_13605])).

tff(c_17927,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17914,c_13617])).

tff(c_17962,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_4592,c_3215,c_17927])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18057,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17962,c_12])).

tff(c_18075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1639,c_18057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.32/4.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.32/4.40  
% 10.32/4.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.32/4.40  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 10.32/4.40  
% 10.32/4.40  %Foreground sorts:
% 10.32/4.40  
% 10.32/4.40  
% 10.32/4.40  %Background operators:
% 10.32/4.40  
% 10.32/4.40  
% 10.32/4.40  %Foreground operators:
% 10.32/4.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.32/4.40  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.32/4.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.32/4.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.32/4.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.32/4.40  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.32/4.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.32/4.40  tff('#skF_2', type, '#skF_2': $i).
% 10.32/4.40  tff('#skF_1', type, '#skF_1': $i).
% 10.32/4.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.32/4.40  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 10.32/4.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.32/4.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.32/4.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.32/4.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.32/4.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.32/4.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.32/4.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.32/4.40  
% 10.32/4.41  tff(f_113, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 10.32/4.41  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 10.32/4.41  tff(f_81, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 10.32/4.41  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.32/4.41  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 10.32/4.41  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 10.32/4.41  tff(f_87, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 10.32/4.41  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.32/4.41  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 10.32/4.41  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.32/4.41  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.32/4.41  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.32/4.41  tff(c_40, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.32/4.41  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.32/4.41  tff(c_1623, plain, (![A_143, B_144]: (k2_pre_topc(A_143, k1_tops_1(A_143, B_144))=B_144 | ~v5_tops_1(B_144, A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.32/4.41  tff(c_1632, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1623])).
% 10.32/4.41  tff(c_1638, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_1632])).
% 10.32/4.41  tff(c_38, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.32/4.41  tff(c_1639, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1638, c_38])).
% 10.32/4.41  tff(c_714, plain, (![A_94, B_95]: (m1_subset_1(k1_tops_1(A_94, B_95), k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.32/4.41  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.32/4.41  tff(c_721, plain, (![A_94, B_95]: (r1_tarski(k1_tops_1(A_94, B_95), u1_struct_0(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_714, c_20])).
% 10.32/4.41  tff(c_22, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.32/4.41  tff(c_368, plain, (![B_70, A_71]: (r1_tarski(B_70, k2_pre_topc(A_71, B_70)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.32/4.41  tff(c_374, plain, (![A_18, A_71]: (r1_tarski(A_18, k2_pre_topc(A_71, A_18)) | ~l1_pre_topc(A_71) | ~r1_tarski(A_18, u1_struct_0(A_71)))), inference(resolution, [status(thm)], [c_22, c_368])).
% 10.32/4.41  tff(c_1645, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1638, c_374])).
% 10.32/4.41  tff(c_1652, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1645])).
% 10.32/4.41  tff(c_1755, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1652])).
% 10.32/4.41  tff(c_1774, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_721, c_1755])).
% 10.32/4.41  tff(c_1778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1774])).
% 10.32/4.41  tff(c_1780, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1652])).
% 10.32/4.41  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(k1_tops_1(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.32/4.41  tff(c_2013, plain, (![A_156, B_157]: (k2_tops_1(A_156, k1_tops_1(A_156, B_157))=k2_tops_1(A_156, B_157) | ~v5_tops_1(B_157, A_156) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.32/4.41  tff(c_2022, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2013])).
% 10.32/4.41  tff(c_2028, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_2022])).
% 10.32/4.41  tff(c_481, plain, (![A_76, B_77]: (m1_subset_1(k2_tops_1(A_76, B_77), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.32/4.41  tff(c_488, plain, (![A_76, B_77]: (r1_tarski(k2_tops_1(A_76, B_77), u1_struct_0(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_481, c_20])).
% 10.32/4.41  tff(c_2032, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2028, c_488])).
% 10.32/4.41  tff(c_2039, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2032])).
% 10.32/4.41  tff(c_4581, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2039])).
% 10.32/4.41  tff(c_4584, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4581])).
% 10.32/4.41  tff(c_4591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4584])).
% 10.32/4.41  tff(c_4592, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_2039])).
% 10.32/4.41  tff(c_1936, plain, (![A_152, B_153]: (k4_subset_1(u1_struct_0(A_152), B_153, k2_tops_1(A_152, B_153))=k2_pre_topc(A_152, B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.32/4.41  tff(c_3193, plain, (![A_194, A_195]: (k4_subset_1(u1_struct_0(A_194), A_195, k2_tops_1(A_194, A_195))=k2_pre_topc(A_194, A_195) | ~l1_pre_topc(A_194) | ~r1_tarski(A_195, u1_struct_0(A_194)))), inference(resolution, [status(thm)], [c_22, c_1936])).
% 10.32/4.41  tff(c_3205, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2028, c_3193])).
% 10.32/4.41  tff(c_3215, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_44, c_1638, c_3205])).
% 10.32/4.41  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(k2_tops_1(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.32/4.41  tff(c_1431, plain, (![A_131, C_132, B_133]: (k4_subset_1(A_131, C_132, B_133)=k4_subset_1(A_131, B_133, C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(A_131)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.32/4.41  tff(c_5604, plain, (![A_274, B_275, B_276]: (k4_subset_1(u1_struct_0(A_274), k2_tops_1(A_274, B_275), B_276)=k4_subset_1(u1_struct_0(A_274), B_276, k2_tops_1(A_274, B_275)) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_274))) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0(A_274))) | ~l1_pre_topc(A_274))), inference(resolution, [status(thm)], [c_32, c_1431])).
% 10.32/4.41  tff(c_17885, plain, (![A_480, B_481, A_482]: (k4_subset_1(u1_struct_0(A_480), k2_tops_1(A_480, B_481), A_482)=k4_subset_1(u1_struct_0(A_480), A_482, k2_tops_1(A_480, B_481)) | ~m1_subset_1(B_481, k1_zfmisc_1(u1_struct_0(A_480))) | ~l1_pre_topc(A_480) | ~r1_tarski(A_482, u1_struct_0(A_480)))), inference(resolution, [status(thm)], [c_22, c_5604])).
% 10.32/4.41  tff(c_17898, plain, (![A_482]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), A_482)=k4_subset_1(u1_struct_0('#skF_1'), A_482, k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_482, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_17885])).
% 10.32/4.41  tff(c_17914, plain, (![A_483]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), A_483)=k4_subset_1(u1_struct_0('#skF_1'), A_483, k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_483, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_17898])).
% 10.32/4.41  tff(c_1259, plain, (![A_117, B_118, C_119]: (k4_subset_1(A_117, B_118, C_119)=k2_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.32/4.41  tff(c_4915, plain, (![A_252, B_253, B_254]: (k4_subset_1(u1_struct_0(A_252), B_253, k1_tops_1(A_252, B_254))=k2_xboole_0(B_253, k1_tops_1(A_252, B_254)) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(resolution, [status(thm)], [c_30, c_1259])).
% 10.32/4.41  tff(c_13592, plain, (![A_434, A_435, B_436]: (k4_subset_1(u1_struct_0(A_434), A_435, k1_tops_1(A_434, B_436))=k2_xboole_0(A_435, k1_tops_1(A_434, B_436)) | ~m1_subset_1(B_436, k1_zfmisc_1(u1_struct_0(A_434))) | ~l1_pre_topc(A_434) | ~r1_tarski(A_435, u1_struct_0(A_434)))), inference(resolution, [status(thm)], [c_22, c_4915])).
% 10.32/4.41  tff(c_13605, plain, (![A_435]: (k4_subset_1(u1_struct_0('#skF_1'), A_435, k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(A_435, k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_435, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_13592])).
% 10.32/4.41  tff(c_13617, plain, (![A_435]: (k4_subset_1(u1_struct_0('#skF_1'), A_435, k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(A_435, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_435, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_13605])).
% 10.32/4.41  tff(c_17927, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_17914, c_13617])).
% 10.32/4.41  tff(c_17962, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_4592, c_3215, c_17927])).
% 10.32/4.41  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.32/4.41  tff(c_18057, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17962, c_12])).
% 10.32/4.41  tff(c_18075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1639, c_18057])).
% 10.32/4.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.32/4.41  
% 10.32/4.41  Inference rules
% 10.32/4.41  ----------------------
% 10.32/4.41  #Ref     : 0
% 10.32/4.41  #Sup     : 4579
% 10.32/4.41  #Fact    : 0
% 10.32/4.41  #Define  : 0
% 10.32/4.41  #Split   : 14
% 10.32/4.41  #Chain   : 0
% 10.32/4.41  #Close   : 0
% 10.32/4.41  
% 10.32/4.41  Ordering : KBO
% 10.32/4.41  
% 10.32/4.41  Simplification rules
% 10.32/4.41  ----------------------
% 10.32/4.41  #Subsume      : 698
% 10.32/4.41  #Demod        : 3233
% 10.32/4.41  #Tautology    : 1873
% 10.32/4.41  #SimpNegUnit  : 1
% 10.32/4.41  #BackRed      : 9
% 10.32/4.41  
% 10.32/4.41  #Partial instantiations: 0
% 10.32/4.41  #Strategies tried      : 1
% 10.32/4.41  
% 10.32/4.41  Timing (in seconds)
% 10.32/4.41  ----------------------
% 10.32/4.42  Preprocessing        : 0.31
% 10.32/4.42  Parsing              : 0.16
% 10.32/4.42  CNF conversion       : 0.02
% 10.32/4.42  Main loop            : 3.34
% 10.32/4.42  Inferencing          : 0.74
% 10.32/4.42  Reduction            : 1.55
% 10.32/4.42  Demodulation         : 1.28
% 10.32/4.42  BG Simplification    : 0.08
% 10.32/4.42  Subsumption          : 0.74
% 10.32/4.42  Abstraction          : 0.14
% 10.32/4.42  MUC search           : 0.00
% 10.32/4.42  Cooper               : 0.00
% 10.32/4.42  Total                : 3.69
% 10.32/4.42  Index Insertion      : 0.00
% 10.32/4.42  Index Deletion       : 0.00
% 10.32/4.42  Index Matching       : 0.00
% 10.32/4.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
