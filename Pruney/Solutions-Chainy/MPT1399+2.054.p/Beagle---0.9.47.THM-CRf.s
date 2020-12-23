%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:26 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 626 expanded)
%              Number of leaves         :   44 ( 222 expanded)
%              Depth                    :   14
%              Number of atoms          :  222 (1818 expanded)
%              Number of equality atoms :   37 ( 278 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_127,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    ! [A_28] :
      ( v4_pre_topc(k2_struct_0(A_28),A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_10] : m1_subset_1('#skF_3',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_18])).

tff(c_30,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_98,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_113,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_30,c_98])).

tff(c_117,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_113])).

tff(c_54,plain,(
    ! [D_41] :
      ( v4_pre_topc(D_41,'#skF_1')
      | ~ r2_hidden(D_41,'#skF_3')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_124,plain,(
    ! [D_55] :
      ( v4_pre_topc(D_55,'#skF_1')
      | ~ r2_hidden(D_55,'#skF_3')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_54])).

tff(c_133,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_124])).

tff(c_135,plain,(
    ~ r2_hidden('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_50,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_3')
      | ~ r2_hidden('#skF_2',D_41)
      | ~ v4_pre_topc(D_41,'#skF_1')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_253,plain,(
    ! [D_75] :
      ( r2_hidden(D_75,'#skF_3')
      | ~ r2_hidden('#skF_2',D_75)
      | ~ v4_pre_topc(D_75,'#skF_1')
      | ~ v3_pre_topc(D_75,'#skF_1')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_50])).

tff(c_257,plain,
    ( r2_hidden('#skF_3','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_253])).

tff(c_264,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_257])).

tff(c_268,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_118,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_42])).

tff(c_10,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_61,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_63,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_6])).

tff(c_157,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_166,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_3') = k4_xboole_0(A_3,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_157])).

tff(c_169,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_3') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_166])).

tff(c_202,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k3_subset_1(A_70,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_205,plain,(
    ! [A_10] : k4_xboole_0(A_10,'#skF_3') = k3_subset_1(A_10,'#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_202])).

tff(c_210,plain,(
    ! [A_10] : k3_subset_1(A_10,'#skF_3') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_205])).

tff(c_20,plain,(
    ! [C_17,A_11,B_15] :
      ( r2_hidden(C_17,k3_subset_1(A_11,B_15))
      | r2_hidden(C_17,B_15)
      | ~ m1_subset_1(C_17,A_11)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_11))
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_269,plain,(
    ! [C_76,A_77,B_78] :
      ( r2_hidden(C_76,k3_subset_1(A_77,B_78))
      | r2_hidden(C_76,B_78)
      | ~ m1_subset_1(C_76,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77))
      | A_77 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_278,plain,(
    ! [C_76,A_10] :
      ( r2_hidden(C_76,A_10)
      | r2_hidden(C_76,'#skF_3')
      | ~ m1_subset_1(C_76,A_10)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_10))
      | A_10 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_269])).

tff(c_299,plain,(
    ! [C_79,A_80] :
      ( r2_hidden(C_79,A_80)
      | r2_hidden(C_79,'#skF_3')
      | ~ m1_subset_1(C_79,A_80)
      | A_80 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_278])).

tff(c_26,plain,(
    ! [B_24,A_23] :
      ( ~ r1_tarski(B_24,A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_322,plain,(
    ! [C_79,A_80] :
      ( ~ r1_tarski('#skF_3',C_79)
      | r2_hidden(C_79,A_80)
      | ~ m1_subset_1(C_79,A_80)
      | A_80 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_299,c_26])).

tff(c_331,plain,(
    ! [C_79,A_80] :
      ( r2_hidden(C_79,A_80)
      | ~ m1_subset_1(C_79,A_80)
      | A_80 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_322])).

tff(c_36,plain,(
    ! [A_29] :
      ( v3_pre_topc(k2_struct_0(A_29),A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_52,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_2',D_41)
      | ~ r2_hidden(D_41,'#skF_3')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_171,plain,(
    ! [D_60] :
      ( r2_hidden('#skF_2',D_60)
      | ~ r2_hidden(D_60,'#skF_3')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_52])).

tff(c_181,plain,
    ( r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_171])).

tff(c_192,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_261,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_253])).

tff(c_267,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_261])).

tff(c_362,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_365,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_362])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_365])).

tff(c_370,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_372,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_375,plain,
    ( ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_331,c_372])).

tff(c_378,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_375])).

tff(c_371,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_380,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_371])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_380])).

tff(c_391,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_410,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_391])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_410])).

tff(c_415,plain,
    ( ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_427,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_429,plain,(
    ! [C_88,A_89,B_90] :
      ( r2_hidden(C_88,k3_subset_1(A_89,B_90))
      | r2_hidden(C_88,B_90)
      | ~ m1_subset_1(C_88,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89))
      | A_89 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_438,plain,(
    ! [C_88,A_10] :
      ( r2_hidden(C_88,A_10)
      | r2_hidden(C_88,'#skF_3')
      | ~ m1_subset_1(C_88,A_10)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_10))
      | A_10 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_429])).

tff(c_459,plain,(
    ! [C_91,A_92] :
      ( r2_hidden(C_91,A_92)
      | r2_hidden(C_91,'#skF_3')
      | ~ m1_subset_1(C_91,A_92)
      | A_92 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_438])).

tff(c_417,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_420,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_417])).

tff(c_424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_420])).

tff(c_425,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_428,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_462,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_459,c_428])).

tff(c_492,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_462])).

tff(c_493,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_492])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_136,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(u1_struct_0(A_56))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_139,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_136])).

tff(c_140,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_139])).

tff(c_141,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_144,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_144])).

tff(c_149,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_510,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_149])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_510])).

tff(c_518,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_531,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_518])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_531])).

tff(c_537,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_545,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_537,c_26])).

tff(c_551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_545])).

tff(c_553,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_560,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_553,c_26])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.48  
% 2.49/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.48  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.48  
% 2.49/1.48  %Foreground sorts:
% 2.49/1.48  
% 2.49/1.48  
% 2.49/1.48  %Background operators:
% 2.49/1.48  
% 2.49/1.48  
% 2.49/1.48  %Foreground operators:
% 2.49/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.49/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.49/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.49/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.49/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.49/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.49/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.49/1.48  
% 2.49/1.50  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.49/1.50  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.49/1.50  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.49/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.49/1.50  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.49/1.50  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.49/1.50  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.49/1.50  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.49/1.50  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.49/1.50  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.49/1.50  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.49/1.50  tff(f_58, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.49/1.50  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.49/1.50  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.49/1.50  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.49/1.50  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.49/1.50  tff(f_87, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.49/1.50  tff(c_38, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.50  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.50  tff(c_62, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8])).
% 2.49/1.50  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.50  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.50  tff(c_34, plain, (![A_28]: (v4_pre_topc(k2_struct_0(A_28), A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.49/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.49/1.50  tff(c_64, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 2.49/1.50  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.49/1.50  tff(c_58, plain, (![A_10]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_18])).
% 2.49/1.50  tff(c_30, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.50  tff(c_98, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.50  tff(c_113, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_30, c_98])).
% 2.49/1.50  tff(c_117, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_113])).
% 2.49/1.50  tff(c_54, plain, (![D_41]: (v4_pre_topc(D_41, '#skF_1') | ~r2_hidden(D_41, '#skF_3') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.50  tff(c_124, plain, (![D_55]: (v4_pre_topc(D_55, '#skF_1') | ~r2_hidden(D_55, '#skF_3') | ~m1_subset_1(D_55, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_54])).
% 2.49/1.50  tff(c_133, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~r2_hidden('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_124])).
% 2.49/1.50  tff(c_135, plain, (~r2_hidden('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_133])).
% 2.49/1.50  tff(c_50, plain, (![D_41]: (r2_hidden(D_41, '#skF_3') | ~r2_hidden('#skF_2', D_41) | ~v4_pre_topc(D_41, '#skF_1') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.50  tff(c_253, plain, (![D_75]: (r2_hidden(D_75, '#skF_3') | ~r2_hidden('#skF_2', D_75) | ~v4_pre_topc(D_75, '#skF_1') | ~v3_pre_topc(D_75, '#skF_1') | ~m1_subset_1(D_75, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_50])).
% 2.49/1.50  tff(c_257, plain, (r2_hidden('#skF_3', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_253])).
% 2.49/1.50  tff(c_264, plain, (~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_135, c_257])).
% 2.49/1.50  tff(c_268, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_264])).
% 2.49/1.50  tff(c_42, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.50  tff(c_118, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_42])).
% 2.49/1.50  tff(c_10, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.49/1.50  tff(c_61, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10])).
% 2.49/1.50  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.49/1.50  tff(c_63, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_6])).
% 2.49/1.50  tff(c_157, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.49/1.50  tff(c_166, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_3')=k4_xboole_0(A_3, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_157])).
% 2.49/1.50  tff(c_169, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_3')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_166])).
% 2.49/1.50  tff(c_202, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k3_subset_1(A_70, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.50  tff(c_205, plain, (![A_10]: (k4_xboole_0(A_10, '#skF_3')=k3_subset_1(A_10, '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_202])).
% 2.49/1.50  tff(c_210, plain, (![A_10]: (k3_subset_1(A_10, '#skF_3')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_205])).
% 2.49/1.50  tff(c_20, plain, (![C_17, A_11, B_15]: (r2_hidden(C_17, k3_subset_1(A_11, B_15)) | r2_hidden(C_17, B_15) | ~m1_subset_1(C_17, A_11) | ~m1_subset_1(B_15, k1_zfmisc_1(A_11)) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.50  tff(c_269, plain, (![C_76, A_77, B_78]: (r2_hidden(C_76, k3_subset_1(A_77, B_78)) | r2_hidden(C_76, B_78) | ~m1_subset_1(C_76, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)) | A_77='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 2.49/1.50  tff(c_278, plain, (![C_76, A_10]: (r2_hidden(C_76, A_10) | r2_hidden(C_76, '#skF_3') | ~m1_subset_1(C_76, A_10) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_10)) | A_10='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_210, c_269])).
% 2.49/1.50  tff(c_299, plain, (![C_79, A_80]: (r2_hidden(C_79, A_80) | r2_hidden(C_79, '#skF_3') | ~m1_subset_1(C_79, A_80) | A_80='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_278])).
% 2.49/1.50  tff(c_26, plain, (![B_24, A_23]: (~r1_tarski(B_24, A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.49/1.50  tff(c_322, plain, (![C_79, A_80]: (~r1_tarski('#skF_3', C_79) | r2_hidden(C_79, A_80) | ~m1_subset_1(C_79, A_80) | A_80='#skF_3')), inference(resolution, [status(thm)], [c_299, c_26])).
% 2.49/1.50  tff(c_331, plain, (![C_79, A_80]: (r2_hidden(C_79, A_80) | ~m1_subset_1(C_79, A_80) | A_80='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_322])).
% 2.49/1.50  tff(c_36, plain, (![A_29]: (v3_pre_topc(k2_struct_0(A_29), A_29) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.49/1.50  tff(c_12, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.49/1.50  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.49/1.50  tff(c_60, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 2.49/1.50  tff(c_52, plain, (![D_41]: (r2_hidden('#skF_2', D_41) | ~r2_hidden(D_41, '#skF_3') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.50  tff(c_171, plain, (![D_60]: (r2_hidden('#skF_2', D_60) | ~r2_hidden(D_60, '#skF_3') | ~m1_subset_1(D_60, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_52])).
% 2.49/1.50  tff(c_181, plain, (r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_60, c_171])).
% 2.49/1.50  tff(c_192, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_181])).
% 2.49/1.50  tff(c_261, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_60, c_253])).
% 2.49/1.50  tff(c_267, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_192, c_261])).
% 2.49/1.50  tff(c_362, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_267])).
% 2.49/1.50  tff(c_365, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_362])).
% 2.49/1.50  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_365])).
% 2.49/1.50  tff(c_370, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_267])).
% 2.49/1.50  tff(c_372, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_370])).
% 2.49/1.50  tff(c_375, plain, (~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_331, c_372])).
% 2.49/1.50  tff(c_378, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_375])).
% 2.49/1.50  tff(c_371, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_267])).
% 2.49/1.50  tff(c_380, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_378, c_371])).
% 2.49/1.50  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_268, c_380])).
% 2.49/1.50  tff(c_391, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_370])).
% 2.49/1.50  tff(c_410, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_391])).
% 2.49/1.50  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_410])).
% 2.49/1.50  tff(c_415, plain, (~v4_pre_topc('#skF_3', '#skF_1') | ~r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_264])).
% 2.49/1.50  tff(c_427, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_415])).
% 2.49/1.50  tff(c_429, plain, (![C_88, A_89, B_90]: (r2_hidden(C_88, k3_subset_1(A_89, B_90)) | r2_hidden(C_88, B_90) | ~m1_subset_1(C_88, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)) | A_89='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 2.49/1.50  tff(c_438, plain, (![C_88, A_10]: (r2_hidden(C_88, A_10) | r2_hidden(C_88, '#skF_3') | ~m1_subset_1(C_88, A_10) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_10)) | A_10='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_210, c_429])).
% 2.49/1.50  tff(c_459, plain, (![C_91, A_92]: (r2_hidden(C_91, A_92) | r2_hidden(C_91, '#skF_3') | ~m1_subset_1(C_91, A_92) | A_92='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_438])).
% 2.49/1.50  tff(c_417, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_267])).
% 2.49/1.50  tff(c_420, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_417])).
% 2.49/1.50  tff(c_424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_420])).
% 2.49/1.50  tff(c_425, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_267])).
% 2.49/1.50  tff(c_428, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_425])).
% 2.49/1.50  tff(c_462, plain, (r2_hidden('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_459, c_428])).
% 2.49/1.50  tff(c_492, plain, (r2_hidden('#skF_2', '#skF_3') | k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_462])).
% 2.49/1.50  tff(c_493, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_427, c_492])).
% 2.49/1.50  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.50  tff(c_136, plain, (![A_56]: (~v1_xboole_0(u1_struct_0(A_56)) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.49/1.50  tff(c_139, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117, c_136])).
% 2.49/1.50  tff(c_140, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_139])).
% 2.49/1.50  tff(c_141, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_140])).
% 2.49/1.50  tff(c_144, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_141])).
% 2.49/1.50  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_144])).
% 2.49/1.50  tff(c_149, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_140])).
% 2.49/1.50  tff(c_510, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_149])).
% 2.49/1.50  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_510])).
% 2.49/1.50  tff(c_518, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_425])).
% 2.49/1.50  tff(c_531, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_518])).
% 2.49/1.50  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_531])).
% 2.49/1.50  tff(c_537, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_415])).
% 2.49/1.50  tff(c_545, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_537, c_26])).
% 2.49/1.50  tff(c_551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_545])).
% 2.49/1.50  tff(c_553, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_181])).
% 2.49/1.50  tff(c_560, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_553, c_26])).
% 2.49/1.50  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_560])).
% 2.49/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.50  
% 2.49/1.50  Inference rules
% 2.49/1.50  ----------------------
% 2.49/1.50  #Ref     : 0
% 2.49/1.50  #Sup     : 83
% 2.49/1.50  #Fact    : 4
% 2.49/1.50  #Define  : 0
% 2.49/1.50  #Split   : 9
% 2.49/1.50  #Chain   : 0
% 2.49/1.50  #Close   : 0
% 2.49/1.50  
% 2.49/1.50  Ordering : KBO
% 2.49/1.50  
% 2.49/1.50  Simplification rules
% 2.49/1.50  ----------------------
% 2.49/1.50  #Subsume      : 8
% 2.49/1.50  #Demod        : 61
% 2.49/1.50  #Tautology    : 38
% 2.49/1.50  #SimpNegUnit  : 5
% 2.49/1.50  #BackRed      : 21
% 2.49/1.50  
% 2.49/1.50  #Partial instantiations: 0
% 2.49/1.50  #Strategies tried      : 1
% 2.49/1.50  
% 2.49/1.50  Timing (in seconds)
% 2.49/1.50  ----------------------
% 2.49/1.51  Preprocessing        : 0.33
% 2.49/1.51  Parsing              : 0.17
% 2.49/1.51  CNF conversion       : 0.02
% 2.49/1.51  Main loop            : 0.27
% 2.49/1.51  Inferencing          : 0.09
% 2.49/1.51  Reduction            : 0.09
% 2.49/1.51  Demodulation         : 0.06
% 2.49/1.51  BG Simplification    : 0.02
% 2.49/1.51  Subsumption          : 0.05
% 2.49/1.51  Abstraction          : 0.01
% 2.49/1.51  MUC search           : 0.00
% 2.49/1.51  Cooper               : 0.00
% 2.49/1.51  Total                : 0.64
% 2.49/1.51  Index Insertion      : 0.00
% 2.49/1.51  Index Deletion       : 0.00
% 2.49/1.51  Index Matching       : 0.00
% 2.49/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
