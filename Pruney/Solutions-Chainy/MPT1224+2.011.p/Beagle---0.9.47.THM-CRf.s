%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:27 EST 2020

% Result     : Theorem 12.05s
% Output     : CNFRefutation 12.05s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 219 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  136 ( 492 expanded)
%              Number of equality atoms :   34 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)),k2_pre_topc(A,k7_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => k2_pre_topc(A,k4_subset_1(u1_struct_0(A),B,C)) = k4_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_240,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_subset_1(A_87,B_88,C_89) = k2_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_269,plain,(
    ! [B_92] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_92,'#skF_2') = k2_xboole_0(B_92,'#skF_2')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_305,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_269])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_pre_topc(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_177,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k2_pre_topc(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_544,plain,(
    ! [A_134,B_135,C_136] :
      ( k7_subset_1(u1_struct_0(A_134),k2_pre_topc(A_134,B_135),C_136) = k4_xboole_0(k2_pre_topc(A_134,B_135),C_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_177,c_14])).

tff(c_561,plain,(
    ! [C_136] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),C_136) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_136)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_544])).

tff(c_595,plain,(
    ! [C_138] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),C_138) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_561])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k7_subset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_601,plain,(
    ! [C_138] :
      ( m1_subset_1(k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_138),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_10])).

tff(c_1226,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_1238,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1226])).

tff(c_1242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_1238])).

tff(c_1244,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_559,plain,(
    ! [C_136] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_136) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_136)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_544])).

tff(c_583,plain,(
    ! [C_137] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_137) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_559])).

tff(c_589,plain,(
    ! [C_137] :
      ( m1_subset_1(k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_137),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_10])).

tff(c_746,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_749,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_746])).

tff(c_753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_749])).

tff(c_755,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] :
      ( k4_subset_1(A_14,B_15,C_16) = k2_xboole_0(B_15,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2326,plain,(
    ! [B_257] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_257,k2_pre_topc('#skF_1','#skF_2')) = k2_xboole_0(B_257,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_755,c_12])).

tff(c_2380,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2')) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1244,c_2326])).

tff(c_18,plain,(
    ! [A_22,B_26,C_28] :
      ( k4_subset_1(u1_struct_0(A_22),k2_pre_topc(A_22,B_26),k2_pre_topc(A_22,C_28)) = k2_pre_topc(A_22,k4_subset_1(u1_struct_0(A_22),B_26,C_28))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2400,plain,
    ( k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2380,c_18])).

tff(c_2407,plain,(
    k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_24,c_305,c_2400])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_37,B_38,C_39] :
      ( r1_tarski(A_37,k2_xboole_0(B_38,C_39))
      | ~ r1_tarski(k4_xboole_0(A_37,B_38),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(resolution,[status(thm)],[c_2,c_39])).

tff(c_2475,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2407,c_43])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    ! [A_58,B_59,C_60] :
      ( k7_subset_1(A_58,B_59,C_60) = k4_xboole_0(B_59,C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_116,plain,(
    ! [C_60] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_60) = k4_xboole_0('#skF_2',C_60) ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_647,plain,(
    ! [A_148,B_149,B_150,C_151] :
      ( k4_subset_1(A_148,B_149,k7_subset_1(A_148,B_150,C_151)) = k2_xboole_0(B_149,k7_subset_1(A_148,B_150,C_151))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_148)) ) ),
    inference(resolution,[status(thm)],[c_10,c_240])).

tff(c_682,plain,(
    ! [B_154,C_155] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',k7_subset_1(u1_struct_0('#skF_1'),B_154,C_155)) = k2_xboole_0('#skF_3',k7_subset_1(u1_struct_0('#skF_1'),B_154,C_155))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_647])).

tff(c_706,plain,(
    ! [C_60] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',k4_xboole_0('#skF_2',C_60)) = k2_xboole_0('#skF_3',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_60))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_682])).

tff(c_718,plain,(
    ! [C_60] : k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',k4_xboole_0('#skF_2',C_60)) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_116,c_706])).

tff(c_137,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k7_subset_1(A_63,B_64,C_65),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    ! [C_60] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_60),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_137])).

tff(c_150,plain,(
    ! [C_60] : m1_subset_1(k4_xboole_0('#skF_2',C_60),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_145])).

tff(c_256,plain,(
    ! [A_20,B_88,B_21] :
      ( k4_subset_1(u1_struct_0(A_20),B_88,k2_pre_topc(A_20,B_21)) = k2_xboole_0(B_88,k2_pre_topc(A_20,B_21))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_16,c_240])).

tff(c_1252,plain,(
    ! [B_21] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_21)) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1244,c_256])).

tff(c_10541,plain,(
    ! [B_658] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_658)) = k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_658))
      | ~ m1_subset_1(B_658,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1252])).

tff(c_10556,plain,(
    ! [B_658] :
      ( k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_658)) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_658))
      | ~ m1_subset_1(B_658,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1(B_658,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10541,c_18])).

tff(c_10629,plain,(
    ! [B_661] :
      ( k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',B_661)) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_661))
      | ~ m1_subset_1(B_661,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_10556])).

tff(c_10696,plain,(
    ! [C_60] : k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2',C_60))) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',k4_xboole_0('#skF_2',C_60))) ),
    inference(resolution,[status(thm)],[c_150,c_10629])).

tff(c_10749,plain,(
    ! [C_60] : k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2',C_60))) = k2_pre_topc('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_60))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_10696])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_578,plain,(
    ! [C_136] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_136) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_559])).

tff(c_20,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_118,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_582,plain,(
    ~ r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_118])).

tff(c_610,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_6,c_582])).

tff(c_10878,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10749,c_610])).

tff(c_10881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2475,c_4,c_10878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:58:56 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.05/4.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.05/4.89  
% 12.05/4.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.05/4.90  %$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 12.05/4.90  
% 12.05/4.90  %Foreground sorts:
% 12.05/4.90  
% 12.05/4.90  
% 12.05/4.90  %Background operators:
% 12.05/4.90  
% 12.05/4.90  
% 12.05/4.90  %Foreground operators:
% 12.05/4.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.05/4.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.05/4.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.05/4.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.05/4.90  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.05/4.90  tff('#skF_2', type, '#skF_2': $i).
% 12.05/4.90  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.05/4.90  tff('#skF_3', type, '#skF_3': $i).
% 12.05/4.90  tff('#skF_1', type, '#skF_1': $i).
% 12.05/4.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.05/4.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.05/4.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.05/4.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.05/4.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.05/4.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.05/4.90  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.05/4.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.05/4.90  
% 12.05/4.91  tff(f_82, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)), k2_pre_topc(A, k7_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tops_1)).
% 12.05/4.91  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.05/4.91  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 12.05/4.91  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 12.05/4.91  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 12.05/4.91  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k4_subset_1(u1_struct_0(A), B, C)) = k4_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_pre_topc)).
% 12.05/4.91  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.05/4.91  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 12.05/4.91  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.05/4.91  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 12.05/4.91  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.05/4.91  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.05/4.91  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.05/4.91  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.05/4.91  tff(c_240, plain, (![A_87, B_88, C_89]: (k4_subset_1(A_87, B_88, C_89)=k2_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.05/4.91  tff(c_269, plain, (![B_92]: (k4_subset_1(u1_struct_0('#skF_1'), B_92, '#skF_2')=k2_xboole_0(B_92, '#skF_2') | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_24, c_240])).
% 12.05/4.91  tff(c_305, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_269])).
% 12.05/4.91  tff(c_16, plain, (![A_20, B_21]: (m1_subset_1(k2_pre_topc(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.05/4.91  tff(c_177, plain, (![A_73, B_74]: (m1_subset_1(k2_pre_topc(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.05/4.91  tff(c_14, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.05/4.91  tff(c_544, plain, (![A_134, B_135, C_136]: (k7_subset_1(u1_struct_0(A_134), k2_pre_topc(A_134, B_135), C_136)=k4_xboole_0(k2_pre_topc(A_134, B_135), C_136) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_177, c_14])).
% 12.05/4.91  tff(c_561, plain, (![C_136]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), C_136)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_136) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_544])).
% 12.05/4.91  tff(c_595, plain, (![C_138]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), C_138)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_138))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_561])).
% 12.05/4.91  tff(c_10, plain, (![A_11, B_12, C_13]: (m1_subset_1(k7_subset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.05/4.91  tff(c_601, plain, (![C_138]: (m1_subset_1(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_138), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_595, c_10])).
% 12.05/4.91  tff(c_1226, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_601])).
% 12.05/4.91  tff(c_1238, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1226])).
% 12.05/4.91  tff(c_1242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_1238])).
% 12.05/4.91  tff(c_1244, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_601])).
% 12.05/4.91  tff(c_559, plain, (![C_136]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_136)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_136) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_544])).
% 12.05/4.91  tff(c_583, plain, (![C_137]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_137)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_137))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_559])).
% 12.05/4.91  tff(c_589, plain, (![C_137]: (m1_subset_1(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_137), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_583, c_10])).
% 12.05/4.91  tff(c_746, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_589])).
% 12.05/4.91  tff(c_749, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_746])).
% 12.05/4.91  tff(c_753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_749])).
% 12.05/4.91  tff(c_755, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_589])).
% 12.05/4.91  tff(c_12, plain, (![A_14, B_15, C_16]: (k4_subset_1(A_14, B_15, C_16)=k2_xboole_0(B_15, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.05/4.91  tff(c_2326, plain, (![B_257]: (k4_subset_1(u1_struct_0('#skF_1'), B_257, k2_pre_topc('#skF_1', '#skF_2'))=k2_xboole_0(B_257, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_755, c_12])).
% 12.05/4.91  tff(c_2380, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2'))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1244, c_2326])).
% 12.05/4.91  tff(c_18, plain, (![A_22, B_26, C_28]: (k4_subset_1(u1_struct_0(A_22), k2_pre_topc(A_22, B_26), k2_pre_topc(A_22, C_28))=k2_pre_topc(A_22, k4_subset_1(u1_struct_0(A_22), B_26, C_28)) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.05/4.91  tff(c_2400, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2380, c_18])).
% 12.05/4.91  tff(c_2407, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_24, c_305, c_2400])).
% 12.05/4.91  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.05/4.91  tff(c_39, plain, (![A_37, B_38, C_39]: (r1_tarski(A_37, k2_xboole_0(B_38, C_39)) | ~r1_tarski(k4_xboole_0(A_37, B_38), C_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.05/4.91  tff(c_43, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_2, c_39])).
% 12.05/4.91  tff(c_2475, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2407, c_43])).
% 12.05/4.91  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.05/4.91  tff(c_111, plain, (![A_58, B_59, C_60]: (k7_subset_1(A_58, B_59, C_60)=k4_xboole_0(B_59, C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.05/4.91  tff(c_116, plain, (![C_60]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_60)=k4_xboole_0('#skF_2', C_60))), inference(resolution, [status(thm)], [c_24, c_111])).
% 12.05/4.91  tff(c_647, plain, (![A_148, B_149, B_150, C_151]: (k4_subset_1(A_148, B_149, k7_subset_1(A_148, B_150, C_151))=k2_xboole_0(B_149, k7_subset_1(A_148, B_150, C_151)) | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)) | ~m1_subset_1(B_150, k1_zfmisc_1(A_148)))), inference(resolution, [status(thm)], [c_10, c_240])).
% 12.05/4.91  tff(c_682, plain, (![B_154, C_155]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', k7_subset_1(u1_struct_0('#skF_1'), B_154, C_155))=k2_xboole_0('#skF_3', k7_subset_1(u1_struct_0('#skF_1'), B_154, C_155)) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_647])).
% 12.05/4.91  tff(c_706, plain, (![C_60]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', k4_xboole_0('#skF_2', C_60))=k2_xboole_0('#skF_3', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_60)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_116, c_682])).
% 12.05/4.91  tff(c_718, plain, (![C_60]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', k4_xboole_0('#skF_2', C_60))=k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_60)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_116, c_706])).
% 12.05/4.91  tff(c_137, plain, (![A_63, B_64, C_65]: (m1_subset_1(k7_subset_1(A_63, B_64, C_65), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.05/4.91  tff(c_145, plain, (![C_60]: (m1_subset_1(k4_xboole_0('#skF_2', C_60), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_116, c_137])).
% 12.05/4.91  tff(c_150, plain, (![C_60]: (m1_subset_1(k4_xboole_0('#skF_2', C_60), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_145])).
% 12.05/4.91  tff(c_256, plain, (![A_20, B_88, B_21]: (k4_subset_1(u1_struct_0(A_20), B_88, k2_pre_topc(A_20, B_21))=k2_xboole_0(B_88, k2_pre_topc(A_20, B_21)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_16, c_240])).
% 12.05/4.91  tff(c_1252, plain, (![B_21]: (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_21))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1244, c_256])).
% 12.05/4.91  tff(c_10541, plain, (![B_658]: (k4_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_658))=k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_658)) | ~m1_subset_1(B_658, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1252])).
% 12.05/4.91  tff(c_10556, plain, (![B_658]: (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_658))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_658)) | ~m1_subset_1(B_658, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(B_658, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_10541, c_18])).
% 12.05/4.91  tff(c_10629, plain, (![B_661]: (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', B_661))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_661)) | ~m1_subset_1(B_661, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_10556])).
% 12.05/4.91  tff(c_10696, plain, (![C_60]: (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', C_60)))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', k4_xboole_0('#skF_2', C_60))))), inference(resolution, [status(thm)], [c_150, c_10629])).
% 12.05/4.91  tff(c_10749, plain, (![C_60]: (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', C_60)))=k2_pre_topc('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_60))))), inference(demodulation, [status(thm), theory('equality')], [c_718, c_10696])).
% 12.05/4.91  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.05/4.91  tff(c_578, plain, (![C_136]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_136)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_136))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_559])).
% 12.05/4.91  tff(c_20, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.05/4.91  tff(c_118, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_20])).
% 12.05/4.91  tff(c_582, plain, (~r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_118])).
% 12.05/4.91  tff(c_610, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_582])).
% 12.05/4.91  tff(c_10878, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_10749, c_610])).
% 12.05/4.91  tff(c_10881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2475, c_4, c_10878])).
% 12.05/4.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.05/4.91  
% 12.05/4.91  Inference rules
% 12.05/4.91  ----------------------
% 12.05/4.91  #Ref     : 0
% 12.05/4.91  #Sup     : 2672
% 12.05/4.91  #Fact    : 0
% 12.05/4.91  #Define  : 0
% 12.05/4.91  #Split   : 4
% 12.05/4.91  #Chain   : 0
% 12.05/4.91  #Close   : 0
% 12.05/4.91  
% 12.05/4.91  Ordering : KBO
% 12.05/4.91  
% 12.05/4.91  Simplification rules
% 12.05/4.91  ----------------------
% 12.05/4.91  #Subsume      : 5
% 12.05/4.91  #Demod        : 1878
% 12.05/4.91  #Tautology    : 843
% 12.05/4.91  #SimpNegUnit  : 0
% 12.05/4.91  #BackRed      : 11
% 12.05/4.91  
% 12.05/4.91  #Partial instantiations: 0
% 12.05/4.91  #Strategies tried      : 1
% 12.05/4.91  
% 12.05/4.91  Timing (in seconds)
% 12.05/4.91  ----------------------
% 12.05/4.92  Preprocessing        : 0.31
% 12.05/4.92  Parsing              : 0.17
% 12.05/4.92  CNF conversion       : 0.02
% 12.05/4.92  Main loop            : 3.83
% 12.05/4.92  Inferencing          : 1.01
% 12.05/4.92  Reduction            : 1.82
% 12.05/4.92  Demodulation         : 1.55
% 12.05/4.92  BG Simplification    : 0.09
% 12.05/4.92  Subsumption          : 0.73
% 12.05/4.92  Abstraction          : 0.16
% 12.05/4.92  MUC search           : 0.00
% 12.05/4.92  Cooper               : 0.00
% 12.05/4.92  Total                : 4.17
% 12.05/4.92  Index Insertion      : 0.00
% 12.05/4.92  Index Deletion       : 0.00
% 12.05/4.92  Index Matching       : 0.00
% 12.05/4.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
