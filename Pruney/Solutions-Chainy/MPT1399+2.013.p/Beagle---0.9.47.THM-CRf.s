%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:20 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 306 expanded)
%              Number of leaves         :   39 ( 118 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 850 expanded)
%              Number of equality atoms :   15 ( 123 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_125,negated_conjecture,(
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

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_30,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_36,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_61,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_26,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_97,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_103,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_26,c_97])).

tff(c_107,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_103])).

tff(c_28,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_112,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_28])).

tff(c_115,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_112])).

tff(c_129,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_132,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_129])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_132])).

tff(c_137,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_108,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_40])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    ! [A_20] :
      ( v4_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_210,plain,(
    ! [B_63,A_64] :
      ( v4_pre_topc(B_63,A_64)
      | ~ v1_xboole_0(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_213,plain,(
    ! [B_63] :
      ( v4_pre_topc(B_63,'#skF_1')
      | ~ v1_xboole_0(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_210])).

tff(c_246,plain,(
    ! [B_67] :
      ( v4_pre_topc(B_67,'#skF_1')
      | ~ v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_213])).

tff(c_250,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_246])).

tff(c_257,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_250])).

tff(c_6,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_59,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_60,plain,(
    ! [A_5] : k3_subset_1(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_57])).

tff(c_265,plain,(
    ! [A_69,B_70] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_69),B_70),A_69)
      | ~ v4_pre_topc(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_272,plain,(
    ! [A_69] :
      ( v3_pre_topc(u1_struct_0(A_69),A_69)
      | ~ v4_pre_topc('#skF_3',A_69)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_265])).

tff(c_277,plain,(
    ! [A_71] :
      ( v3_pre_topc(u1_struct_0(A_71),A_71)
      | ~ v4_pre_topc('#skF_3',A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_272])).

tff(c_280,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_277])).

tff(c_282,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_257,c_280])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_52,plain,(
    ! [D_35] :
      ( v4_pre_topc(D_35,'#skF_1')
      | ~ r2_hidden(D_35,'#skF_3')
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_118,plain,(
    ! [D_48] :
      ( v4_pre_topc(D_48,'#skF_1')
      | ~ r2_hidden(D_48,'#skF_3')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_52])).

tff(c_128,plain,
    ( v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_118])).

tff(c_174,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_48,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_3')
      | ~ r2_hidden('#skF_2',D_35)
      | ~ v4_pre_topc(D_35,'#skF_1')
      | ~ v3_pre_topc(D_35,'#skF_1')
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_230,plain,(
    ! [D_66] :
      ( r2_hidden(D_66,'#skF_3')
      | ~ r2_hidden('#skF_2',D_66)
      | ~ v4_pre_topc(D_66,'#skF_1')
      | ~ v3_pre_topc(D_66,'#skF_1')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_48])).

tff(c_238,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_230])).

tff(c_244,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_238])).

tff(c_284,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_244])).

tff(c_285,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_295,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_285])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_295])).

tff(c_300,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_304,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_300])).

tff(c_307,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_304])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_307])).

tff(c_311,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_314,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_311,c_20])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.34  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.34  
% 2.33/1.34  %Foreground sorts:
% 2.33/1.34  
% 2.33/1.34  
% 2.33/1.34  %Background operators:
% 2.33/1.34  
% 2.33/1.34  
% 2.33/1.34  %Foreground operators:
% 2.33/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.33/1.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.33/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.33/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.33/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.34  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.33/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.33/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.33/1.34  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.33/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.33/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.34  
% 2.33/1.36  tff(f_125, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.33/1.36  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.33/1.36  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.33/1.36  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.33/1.36  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.33/1.36  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.33/1.36  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.33/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.33/1.36  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.33/1.36  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.33/1.36  tff(f_30, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.33/1.36  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.33/1.36  tff(f_36, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.33/1.36  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 2.33/1.36  tff(f_34, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.33/1.36  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.33/1.36  tff(c_36, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.33/1.36  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.33/1.36  tff(c_61, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4])).
% 2.33/1.36  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.33/1.36  tff(c_26, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.33/1.36  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.33/1.36  tff(c_97, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.33/1.36  tff(c_103, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_26, c_97])).
% 2.33/1.36  tff(c_107, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_103])).
% 2.33/1.36  tff(c_28, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.33/1.36  tff(c_112, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107, c_28])).
% 2.33/1.36  tff(c_115, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_46, c_112])).
% 2.33/1.36  tff(c_129, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_115])).
% 2.33/1.36  tff(c_132, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_129])).
% 2.33/1.36  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_132])).
% 2.33/1.36  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_115])).
% 2.33/1.36  tff(c_40, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.33/1.36  tff(c_108, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_40])).
% 2.33/1.36  tff(c_16, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.33/1.36  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.33/1.36  tff(c_30, plain, (![A_20]: (v4_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.33/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.33/1.36  tff(c_62, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2])).
% 2.33/1.36  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.36  tff(c_55, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_14])).
% 2.33/1.36  tff(c_210, plain, (![B_63, A_64]: (v4_pre_topc(B_63, A_64) | ~v1_xboole_0(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.33/1.36  tff(c_213, plain, (![B_63]: (v4_pre_topc(B_63, '#skF_1') | ~v1_xboole_0(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_210])).
% 2.33/1.36  tff(c_246, plain, (![B_67]: (v4_pre_topc(B_67, '#skF_1') | ~v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_213])).
% 2.33/1.36  tff(c_250, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_55, c_246])).
% 2.33/1.36  tff(c_257, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_250])).
% 2.33/1.36  tff(c_6, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.33/1.36  tff(c_59, plain, (![A_2]: (k1_subset_1(A_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 2.33/1.36  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.36  tff(c_12, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.33/1.36  tff(c_57, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 2.33/1.36  tff(c_60, plain, (![A_5]: (k3_subset_1(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_57])).
% 2.33/1.36  tff(c_265, plain, (![A_69, B_70]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_69), B_70), A_69) | ~v4_pre_topc(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.33/1.36  tff(c_272, plain, (![A_69]: (v3_pre_topc(u1_struct_0(A_69), A_69) | ~v4_pre_topc('#skF_3', A_69) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(superposition, [status(thm), theory('equality')], [c_60, c_265])).
% 2.33/1.36  tff(c_277, plain, (![A_71]: (v3_pre_topc(u1_struct_0(A_71), A_71) | ~v4_pre_topc('#skF_3', A_71) | ~l1_pre_topc(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_272])).
% 2.33/1.36  tff(c_280, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107, c_277])).
% 2.33/1.36  tff(c_282, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_257, c_280])).
% 2.33/1.36  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.33/1.36  tff(c_58, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.33/1.36  tff(c_52, plain, (![D_35]: (v4_pre_topc(D_35, '#skF_1') | ~r2_hidden(D_35, '#skF_3') | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.33/1.36  tff(c_118, plain, (![D_48]: (v4_pre_topc(D_48, '#skF_1') | ~r2_hidden(D_48, '#skF_3') | ~m1_subset_1(D_48, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_52])).
% 2.33/1.36  tff(c_128, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_58, c_118])).
% 2.33/1.36  tff(c_174, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_128])).
% 2.33/1.36  tff(c_48, plain, (![D_35]: (r2_hidden(D_35, '#skF_3') | ~r2_hidden('#skF_2', D_35) | ~v4_pre_topc(D_35, '#skF_1') | ~v3_pre_topc(D_35, '#skF_1') | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.33/1.36  tff(c_230, plain, (![D_66]: (r2_hidden(D_66, '#skF_3') | ~r2_hidden('#skF_2', D_66) | ~v4_pre_topc(D_66, '#skF_1') | ~v3_pre_topc(D_66, '#skF_1') | ~m1_subset_1(D_66, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_48])).
% 2.33/1.36  tff(c_238, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_58, c_230])).
% 2.33/1.36  tff(c_244, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_174, c_238])).
% 2.33/1.36  tff(c_284, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_244])).
% 2.33/1.36  tff(c_285, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_284])).
% 2.33/1.36  tff(c_295, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_285])).
% 2.33/1.36  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_295])).
% 2.33/1.36  tff(c_300, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_284])).
% 2.33/1.36  tff(c_304, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_300])).
% 2.33/1.36  tff(c_307, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_304])).
% 2.33/1.36  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_307])).
% 2.33/1.36  tff(c_311, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_128])).
% 2.33/1.36  tff(c_20, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.36  tff(c_314, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_311, c_20])).
% 2.33/1.36  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_314])).
% 2.33/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.36  
% 2.33/1.36  Inference rules
% 2.33/1.36  ----------------------
% 2.33/1.36  #Ref     : 0
% 2.33/1.36  #Sup     : 44
% 2.33/1.36  #Fact    : 0
% 2.33/1.36  #Define  : 0
% 2.33/1.36  #Split   : 5
% 2.33/1.36  #Chain   : 0
% 2.33/1.36  #Close   : 0
% 2.33/1.36  
% 2.33/1.36  Ordering : KBO
% 2.33/1.36  
% 2.33/1.36  Simplification rules
% 2.33/1.36  ----------------------
% 2.33/1.36  #Subsume      : 6
% 2.33/1.36  #Demod        : 39
% 2.33/1.36  #Tautology    : 18
% 2.33/1.36  #SimpNegUnit  : 4
% 2.33/1.36  #BackRed      : 1
% 2.33/1.36  
% 2.33/1.36  #Partial instantiations: 0
% 2.33/1.36  #Strategies tried      : 1
% 2.33/1.36  
% 2.33/1.36  Timing (in seconds)
% 2.33/1.36  ----------------------
% 2.33/1.36  Preprocessing        : 0.33
% 2.33/1.36  Parsing              : 0.18
% 2.33/1.36  CNF conversion       : 0.02
% 2.33/1.36  Main loop            : 0.20
% 2.33/1.36  Inferencing          : 0.07
% 2.33/1.36  Reduction            : 0.06
% 2.33/1.36  Demodulation         : 0.05
% 2.33/1.36  BG Simplification    : 0.01
% 2.33/1.36  Subsumption          : 0.03
% 2.33/1.36  Abstraction          : 0.01
% 2.33/1.36  MUC search           : 0.00
% 2.33/1.36  Cooper               : 0.00
% 2.33/1.36  Total                : 0.57
% 2.33/1.36  Index Insertion      : 0.00
% 2.33/1.36  Index Deletion       : 0.00
% 2.33/1.36  Index Matching       : 0.00
% 2.33/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
