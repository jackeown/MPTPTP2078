%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:26 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 428 expanded)
%              Number of leaves         :   47 ( 163 expanded)
%              Depth                    :   14
%              Number of atoms          :  194 (1236 expanded)
%              Number of equality atoms :   22 ( 183 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( m1_connsp_2(D,A,C)
                            & r1_tarski(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(c_50,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_4] : r1_tarski('#skF_5',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_28,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_119,plain,(
    ! [A_72] :
      ( u1_struct_0(A_72) = k2_struct_0(A_72)
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,(
    ! [A_77] :
      ( u1_struct_0(A_77) = k2_struct_0(A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_28,c_119])).

tff(c_139,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_135])).

tff(c_158,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(u1_struct_0(A_79))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_161,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_158])).

tff(c_162,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_161])).

tff(c_163,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_166,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_163])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_166])).

tff(c_171,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_153,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_54])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_32,plain,(
    ! [A_23] :
      ( v3_pre_topc(k2_struct_0(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [A_71] : m1_subset_1('#skF_5',k1_zfmisc_1(A_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_68,plain,(
    ! [D_63] :
      ( v3_pre_topc(D_63,'#skF_3')
      | ~ r2_hidden(D_63,'#skF_5')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_118,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_68])).

tff(c_134,plain,(
    ~ r2_hidden('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_69,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_62,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,'#skF_5')
      | ~ r2_hidden('#skF_4',D_63)
      | ~ v4_pre_topc(D_63,'#skF_3')
      | ~ v3_pre_topc(D_63,'#skF_3')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_268,plain,(
    ! [D_91] :
      ( r2_hidden(D_91,'#skF_5')
      | ~ r2_hidden('#skF_4',D_91)
      | ~ v4_pre_topc(D_91,'#skF_3')
      | ~ v3_pre_topc(D_91,'#skF_3')
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_62])).

tff(c_272,plain,
    ( r2_hidden('#skF_5','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_268])).

tff(c_279,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_272])).

tff(c_592,plain,(
    ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_676,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_2'(A_141,B_142),B_142)
      | v3_pre_topc(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_678,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_2'('#skF_3',B_142),B_142)
      | v3_pre_topc(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_676])).

tff(c_686,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_2'('#skF_3',B_142),B_142)
      | v3_pre_topc(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_678])).

tff(c_690,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_2'('#skF_3',B_143),B_143)
      | v3_pre_topc(B_143,'#skF_3')
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_686])).

tff(c_693,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_5'),'#skF_5')
    | v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_690])).

tff(c_699,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_693])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_708,plain,(
    ~ r1_tarski('#skF_5','#skF_2'('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_699,c_24])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_708])).

tff(c_716,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_5') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_4])).

tff(c_173,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_182,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_5') = k4_xboole_0(A_3,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_173])).

tff(c_185,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_5') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_182])).

tff(c_225,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_228,plain,(
    ! [A_10] : k4_xboole_0(A_10,'#skF_5') = k3_subset_1(A_10,'#skF_5') ),
    inference(resolution,[status(thm)],[c_69,c_225])).

tff(c_233,plain,(
    ! [A_10] : k3_subset_1(A_10,'#skF_5') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_228])).

tff(c_752,plain,(
    ! [A_152,B_153] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_152),B_153),A_152)
      | ~ v3_pre_topc(B_153,A_152)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_756,plain,(
    ! [A_152] :
      ( v4_pre_topc(u1_struct_0(A_152),A_152)
      | ~ v3_pre_topc('#skF_5',A_152)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_752])).

tff(c_764,plain,(
    ! [A_154] :
      ( v4_pre_topc(u1_struct_0(A_154),A_154)
      | ~ v3_pre_topc('#skF_5',A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_756])).

tff(c_767,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_764])).

tff(c_769,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_716,c_767])).

tff(c_10,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_99,plain,(
    ! [D_68] :
      ( v3_pre_topc(D_68,'#skF_3')
      | ~ r2_hidden(D_68,'#skF_5')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_104,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_99])).

tff(c_223,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_104])).

tff(c_224,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_276,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_268])).

tff(c_282,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_276])).

tff(c_771,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_282])).

tff(c_772,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_782,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_772])).

tff(c_786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_782])).

tff(c_787,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_791,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_787])).

tff(c_794,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_791])).

tff(c_796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_794])).

tff(c_798,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_801,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_798,c_24])).

tff(c_805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:47:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.43  
% 2.69/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.43  %$ m1_connsp_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.05/1.43  
% 3.05/1.43  %Foreground sorts:
% 3.05/1.43  
% 3.05/1.43  
% 3.05/1.43  %Background operators:
% 3.05/1.43  
% 3.05/1.43  
% 3.05/1.43  %Foreground operators:
% 3.05/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.05/1.43  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.05/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.05/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.05/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.05/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.05/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.05/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.05/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.05/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.05/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.05/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.05/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.05/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.05/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.05/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.05/1.43  
% 3.05/1.45  tff(f_147, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.05/1.45  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.05/1.45  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.05/1.45  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.05/1.45  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.05/1.45  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.05/1.45  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.05/1.45  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.05/1.45  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 3.05/1.45  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.05/1.45  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.05/1.45  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.05/1.45  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.05/1.45  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.05/1.45  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 3.05/1.45  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.05/1.45  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.05/1.45  tff(c_50, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.05/1.45  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.45  tff(c_73, plain, (![A_4]: (r1_tarski('#skF_5', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6])).
% 3.05/1.45  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.05/1.45  tff(c_28, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.05/1.45  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.05/1.45  tff(c_119, plain, (![A_72]: (u1_struct_0(A_72)=k2_struct_0(A_72) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.05/1.45  tff(c_135, plain, (![A_77]: (u1_struct_0(A_77)=k2_struct_0(A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_28, c_119])).
% 3.05/1.45  tff(c_139, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_135])).
% 3.05/1.45  tff(c_158, plain, (![A_79]: (~v1_xboole_0(u1_struct_0(A_79)) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.45  tff(c_161, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_139, c_158])).
% 3.05/1.45  tff(c_162, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_161])).
% 3.05/1.45  tff(c_163, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_162])).
% 3.05/1.45  tff(c_166, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_163])).
% 3.05/1.45  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_166])).
% 3.05/1.45  tff(c_171, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_162])).
% 3.05/1.45  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.05/1.45  tff(c_153, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_54])).
% 3.05/1.45  tff(c_20, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.05/1.45  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.05/1.45  tff(c_32, plain, (![A_23]: (v3_pre_topc(k2_struct_0(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.05/1.45  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.45  tff(c_113, plain, (![A_71]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 3.05/1.45  tff(c_68, plain, (![D_63]: (v3_pre_topc(D_63, '#skF_3') | ~r2_hidden(D_63, '#skF_5') | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.05/1.45  tff(c_118, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~r2_hidden('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_113, c_68])).
% 3.05/1.45  tff(c_134, plain, (~r2_hidden('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_118])).
% 3.05/1.45  tff(c_69, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 3.05/1.45  tff(c_62, plain, (![D_63]: (r2_hidden(D_63, '#skF_5') | ~r2_hidden('#skF_4', D_63) | ~v4_pre_topc(D_63, '#skF_3') | ~v3_pre_topc(D_63, '#skF_3') | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.05/1.45  tff(c_268, plain, (![D_91]: (r2_hidden(D_91, '#skF_5') | ~r2_hidden('#skF_4', D_91) | ~v4_pre_topc(D_91, '#skF_3') | ~v3_pre_topc(D_91, '#skF_3') | ~m1_subset_1(D_91, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_62])).
% 3.05/1.45  tff(c_272, plain, (r2_hidden('#skF_5', '#skF_5') | ~r2_hidden('#skF_4', '#skF_5') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_69, c_268])).
% 3.05/1.45  tff(c_279, plain, (~r2_hidden('#skF_4', '#skF_5') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_134, c_272])).
% 3.05/1.45  tff(c_592, plain, (~v3_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_279])).
% 3.05/1.45  tff(c_676, plain, (![A_141, B_142]: (r2_hidden('#skF_2'(A_141, B_142), B_142) | v3_pre_topc(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.05/1.45  tff(c_678, plain, (![B_142]: (r2_hidden('#skF_2'('#skF_3', B_142), B_142) | v3_pre_topc(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_676])).
% 3.05/1.45  tff(c_686, plain, (![B_142]: (r2_hidden('#skF_2'('#skF_3', B_142), B_142) | v3_pre_topc(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_678])).
% 3.05/1.45  tff(c_690, plain, (![B_143]: (r2_hidden('#skF_2'('#skF_3', B_143), B_143) | v3_pre_topc(B_143, '#skF_3') | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_686])).
% 3.05/1.45  tff(c_693, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_5'), '#skF_5') | v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_69, c_690])).
% 3.05/1.45  tff(c_699, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_592, c_693])).
% 3.05/1.45  tff(c_24, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.05/1.45  tff(c_708, plain, (~r1_tarski('#skF_5', '#skF_2'('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_699, c_24])).
% 3.05/1.45  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_708])).
% 3.05/1.45  tff(c_716, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_279])).
% 3.05/1.45  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.45  tff(c_72, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_5')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8])).
% 3.05/1.45  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.05/1.45  tff(c_74, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_4])).
% 3.05/1.45  tff(c_173, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.45  tff(c_182, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_5')=k4_xboole_0(A_3, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_173])).
% 3.05/1.45  tff(c_185, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_5')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_182])).
% 3.05/1.45  tff(c_225, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.45  tff(c_228, plain, (![A_10]: (k4_xboole_0(A_10, '#skF_5')=k3_subset_1(A_10, '#skF_5'))), inference(resolution, [status(thm)], [c_69, c_225])).
% 3.05/1.45  tff(c_233, plain, (![A_10]: (k3_subset_1(A_10, '#skF_5')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_228])).
% 3.05/1.45  tff(c_752, plain, (![A_152, B_153]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_152), B_153), A_152) | ~v3_pre_topc(B_153, A_152) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.05/1.45  tff(c_756, plain, (![A_152]: (v4_pre_topc(u1_struct_0(A_152), A_152) | ~v3_pre_topc('#skF_5', A_152) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(superposition, [status(thm), theory('equality')], [c_233, c_752])).
% 3.05/1.45  tff(c_764, plain, (![A_154]: (v4_pre_topc(u1_struct_0(A_154), A_154) | ~v3_pre_topc('#skF_5', A_154) | ~l1_pre_topc(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_756])).
% 3.05/1.45  tff(c_767, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_139, c_764])).
% 3.05/1.45  tff(c_769, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_716, c_767])).
% 3.05/1.45  tff(c_10, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.45  tff(c_14, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.45  tff(c_71, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 3.05/1.45  tff(c_99, plain, (![D_68]: (v3_pre_topc(D_68, '#skF_3') | ~r2_hidden(D_68, '#skF_5') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.05/1.45  tff(c_104, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~r2_hidden(u1_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_71, c_99])).
% 3.05/1.45  tff(c_223, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_104])).
% 3.05/1.45  tff(c_224, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_223])).
% 3.05/1.45  tff(c_276, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_71, c_268])).
% 3.05/1.45  tff(c_282, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_224, c_276])).
% 3.05/1.45  tff(c_771, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_769, c_282])).
% 3.05/1.45  tff(c_772, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_771])).
% 3.05/1.45  tff(c_782, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_772])).
% 3.05/1.45  tff(c_786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_782])).
% 3.05/1.45  tff(c_787, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_771])).
% 3.05/1.45  tff(c_791, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_787])).
% 3.05/1.45  tff(c_794, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_791])).
% 3.05/1.45  tff(c_796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_794])).
% 3.05/1.45  tff(c_798, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_223])).
% 3.05/1.45  tff(c_801, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_798, c_24])).
% 3.05/1.45  tff(c_805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_801])).
% 3.05/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.45  
% 3.05/1.45  Inference rules
% 3.05/1.45  ----------------------
% 3.05/1.45  #Ref     : 0
% 3.05/1.45  #Sup     : 130
% 3.05/1.45  #Fact    : 0
% 3.05/1.45  #Define  : 0
% 3.05/1.45  #Split   : 15
% 3.05/1.45  #Chain   : 0
% 3.05/1.45  #Close   : 0
% 3.05/1.45  
% 3.05/1.45  Ordering : KBO
% 3.05/1.45  
% 3.05/1.45  Simplification rules
% 3.05/1.45  ----------------------
% 3.05/1.45  #Subsume      : 28
% 3.05/1.45  #Demod        : 86
% 3.05/1.45  #Tautology    : 43
% 3.05/1.45  #SimpNegUnit  : 19
% 3.05/1.45  #BackRed      : 3
% 3.05/1.45  
% 3.05/1.45  #Partial instantiations: 0
% 3.05/1.45  #Strategies tried      : 1
% 3.05/1.45  
% 3.05/1.45  Timing (in seconds)
% 3.05/1.45  ----------------------
% 3.05/1.46  Preprocessing        : 0.34
% 3.05/1.46  Parsing              : 0.18
% 3.05/1.46  CNF conversion       : 0.03
% 3.05/1.46  Main loop            : 0.34
% 3.05/1.46  Inferencing          : 0.12
% 3.05/1.46  Reduction            : 0.11
% 3.05/1.46  Demodulation         : 0.08
% 3.05/1.46  BG Simplification    : 0.02
% 3.05/1.46  Subsumption          : 0.06
% 3.05/1.46  Abstraction          : 0.01
% 3.05/1.46  MUC search           : 0.00
% 3.05/1.46  Cooper               : 0.00
% 3.05/1.46  Total                : 0.72
% 3.05/1.46  Index Insertion      : 0.00
% 3.05/1.46  Index Deletion       : 0.00
% 3.05/1.46  Index Matching       : 0.00
% 3.05/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
