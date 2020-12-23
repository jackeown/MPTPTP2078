%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:30 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 220 expanded)
%              Number of leaves         :   32 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  162 ( 472 expanded)
%              Number of equality atoms :   16 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_38,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_61,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_70,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_71,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_40])).

tff(c_89,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,B_39)
      | v1_xboole_0(B_39)
      | ~ m1_subset_1(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [A_48,A_49] :
      ( r1_tarski(A_48,A_49)
      | v1_xboole_0(k1_zfmisc_1(A_49))
      | ~ m1_subset_1(A_48,k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_89,c_8])).

tff(c_129,plain,
    ( r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_71,c_122])).

tff(c_132,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_95,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_102,plain,(
    ! [A_43,A_44] :
      ( ~ v1_xboole_0(A_43)
      | ~ r2_hidden(A_44,A_43) ) ),
    inference(resolution,[status(thm)],[c_47,c_95])).

tff(c_110,plain,(
    ! [A_3,C_7] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_149,plain,(
    ! [C_52] : ~ r1_tarski(C_52,k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_132,c_110])).

tff(c_159,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_160,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_17] :
      ( k1_tops_1(A_17,k2_struct_0(A_17)) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_268,plain,(
    ! [C_80,A_81,B_82] :
      ( m2_connsp_2(C_80,A_81,B_82)
      | ~ r1_tarski(B_82,k1_tops_1(A_81,C_80))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_381,plain,(
    ! [C_90,A_91] :
      ( m2_connsp_2(C_90,A_91,k1_tops_1(A_91,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(k1_tops_1(A_91,C_90),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_385,plain,(
    ! [C_90] :
      ( m2_connsp_2(C_90,'#skF_3',k1_tops_1('#skF_3',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k1_tops_1('#skF_3',C_90),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_381])).

tff(c_388,plain,(
    ! [C_92] :
      ( m2_connsp_2(C_92,'#skF_3',k1_tops_1('#skF_3',C_92))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k1_tops_1('#skF_3',C_92),k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_70,c_385])).

tff(c_391,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',k1_tops_1('#skF_3',k2_struct_0('#skF_3')))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_388])).

tff(c_393,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',k1_tops_1('#skF_3',k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_47,c_47,c_391])).

tff(c_396,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',k2_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_393])).

tff(c_398,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_396])).

tff(c_205,plain,(
    ! [B_67,A_68,C_69] :
      ( r1_tarski(B_67,k1_tops_1(A_68,C_69))
      | ~ m2_connsp_2(C_69,A_68,B_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_207,plain,(
    ! [B_67,C_69] :
      ( r1_tarski(B_67,k1_tops_1('#skF_3',C_69))
      | ~ m2_connsp_2(C_69,'#skF_3',B_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_205])).

tff(c_295,plain,(
    ! [B_83,C_84] :
      ( r1_tarski(B_83,k1_tops_1('#skF_3',C_84))
      | ~ m2_connsp_2(C_84,'#skF_3',B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_70,c_207])).

tff(c_315,plain,(
    ! [B_86] :
      ( r1_tarski(B_86,k1_tops_1('#skF_3',k2_struct_0('#skF_3')))
      | ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_47,c_295])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_399,plain,(
    ! [B_93] :
      ( k1_tops_1('#skF_3',k2_struct_0('#skF_3')) = B_93
      | ~ r1_tarski(k1_tops_1('#skF_3',k2_struct_0('#skF_3')),B_93)
      | ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_315,c_2])).

tff(c_410,plain,(
    ! [B_93] :
      ( k1_tops_1('#skF_3',k2_struct_0('#skF_3')) = B_93
      | ~ r1_tarski(k2_struct_0('#skF_3'),B_93)
      | ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_399])).

tff(c_426,plain,(
    ! [B_94] :
      ( k1_tops_1('#skF_3',k2_struct_0('#skF_3')) = B_94
      | ~ r1_tarski(k2_struct_0('#skF_3'),B_94)
      | ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_410])).

tff(c_433,plain,
    ( k1_tops_1('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'))
    | ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_47,c_426])).

tff(c_437,plain,(
    k1_tops_1('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_6,c_433])).

tff(c_34,plain,(
    ! [C_24,A_18,B_22] :
      ( m2_connsp_2(C_24,A_18,B_22)
      | ~ r1_tarski(B_22,k1_tops_1(A_18,C_24))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_449,plain,(
    ! [B_22] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_22)
      | ~ r1_tarski(B_22,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_34])).

tff(c_471,plain,(
    ! [B_95] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_95)
      | ~ r1_tarski(B_95,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_70,c_47,c_70,c_449])).

tff(c_474,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_471])).

tff(c_481,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_474])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:20:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.43  
% 2.61/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.44  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.61/1.44  
% 2.61/1.44  %Foreground sorts:
% 2.61/1.44  
% 2.61/1.44  
% 2.61/1.44  %Background operators:
% 2.61/1.44  
% 2.61/1.44  
% 2.61/1.44  %Foreground operators:
% 2.61/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.44  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.61/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.61/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.61/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.61/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.61/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.44  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.61/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.44  
% 2.61/1.45  tff(f_96, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.61/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.45  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.61/1.45  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.61/1.45  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.61/1.45  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.61/1.45  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.61/1.45  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.61/1.45  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.61/1.45  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.61/1.45  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.61/1.45  tff(c_38, plain, (~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.45  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.45  tff(c_30, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.45  tff(c_61, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.45  tff(c_66, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_30, c_61])).
% 2.61/1.45  tff(c_70, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_66])).
% 2.61/1.45  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.45  tff(c_71, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_40])).
% 2.61/1.45  tff(c_89, plain, (![A_38, B_39]: (r2_hidden(A_38, B_39) | v1_xboole_0(B_39) | ~m1_subset_1(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.61/1.45  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.45  tff(c_122, plain, (![A_48, A_49]: (r1_tarski(A_48, A_49) | v1_xboole_0(k1_zfmisc_1(A_49)) | ~m1_subset_1(A_48, k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_89, c_8])).
% 2.61/1.45  tff(c_129, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_71, c_122])).
% 2.61/1.45  tff(c_132, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_129])).
% 2.61/1.45  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.45  tff(c_20, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.61/1.45  tff(c_22, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.45  tff(c_47, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.61/1.45  tff(c_95, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.45  tff(c_102, plain, (![A_43, A_44]: (~v1_xboole_0(A_43) | ~r2_hidden(A_44, A_43))), inference(resolution, [status(thm)], [c_47, c_95])).
% 2.61/1.45  tff(c_110, plain, (![A_3, C_7]: (~v1_xboole_0(k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_10, c_102])).
% 2.61/1.45  tff(c_149, plain, (![C_52]: (~r1_tarski(C_52, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_132, c_110])).
% 2.61/1.45  tff(c_159, plain, $false, inference(resolution, [status(thm)], [c_6, c_149])).
% 2.61/1.45  tff(c_160, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_129])).
% 2.61/1.45  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.45  tff(c_32, plain, (![A_17]: (k1_tops_1(A_17, k2_struct_0(A_17))=k2_struct_0(A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.45  tff(c_268, plain, (![C_80, A_81, B_82]: (m2_connsp_2(C_80, A_81, B_82) | ~r1_tarski(B_82, k1_tops_1(A_81, C_80)) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.45  tff(c_381, plain, (![C_90, A_91]: (m2_connsp_2(C_90, A_91, k1_tops_1(A_91, C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(k1_tops_1(A_91, C_90), k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(resolution, [status(thm)], [c_6, c_268])).
% 2.61/1.45  tff(c_385, plain, (![C_90]: (m2_connsp_2(C_90, '#skF_3', k1_tops_1('#skF_3', C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k1_tops_1('#skF_3', C_90), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_381])).
% 2.61/1.45  tff(c_388, plain, (![C_92]: (m2_connsp_2(C_92, '#skF_3', k1_tops_1('#skF_3', C_92)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k1_tops_1('#skF_3', C_92), k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_70, c_385])).
% 2.61/1.45  tff(c_391, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', k1_tops_1('#skF_3', k2_struct_0('#skF_3'))) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_388])).
% 2.61/1.45  tff(c_393, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', k1_tops_1('#skF_3', k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_47, c_47, c_391])).
% 2.61/1.45  tff(c_396, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', k2_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_393])).
% 2.61/1.45  tff(c_398, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_396])).
% 2.61/1.45  tff(c_205, plain, (![B_67, A_68, C_69]: (r1_tarski(B_67, k1_tops_1(A_68, C_69)) | ~m2_connsp_2(C_69, A_68, B_67) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.45  tff(c_207, plain, (![B_67, C_69]: (r1_tarski(B_67, k1_tops_1('#skF_3', C_69)) | ~m2_connsp_2(C_69, '#skF_3', B_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_205])).
% 2.61/1.45  tff(c_295, plain, (![B_83, C_84]: (r1_tarski(B_83, k1_tops_1('#skF_3', C_84)) | ~m2_connsp_2(C_84, '#skF_3', B_83) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_70, c_207])).
% 2.61/1.45  tff(c_315, plain, (![B_86]: (r1_tarski(B_86, k1_tops_1('#skF_3', k2_struct_0('#skF_3'))) | ~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_47, c_295])).
% 2.61/1.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.45  tff(c_399, plain, (![B_93]: (k1_tops_1('#skF_3', k2_struct_0('#skF_3'))=B_93 | ~r1_tarski(k1_tops_1('#skF_3', k2_struct_0('#skF_3')), B_93) | ~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_315, c_2])).
% 2.61/1.45  tff(c_410, plain, (![B_93]: (k1_tops_1('#skF_3', k2_struct_0('#skF_3'))=B_93 | ~r1_tarski(k2_struct_0('#skF_3'), B_93) | ~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_399])).
% 2.61/1.45  tff(c_426, plain, (![B_94]: (k1_tops_1('#skF_3', k2_struct_0('#skF_3'))=B_94 | ~r1_tarski(k2_struct_0('#skF_3'), B_94) | ~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_410])).
% 2.61/1.45  tff(c_433, plain, (k1_tops_1('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3')) | ~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_47, c_426])).
% 2.61/1.45  tff(c_437, plain, (k1_tops_1('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_6, c_433])).
% 2.61/1.45  tff(c_34, plain, (![C_24, A_18, B_22]: (m2_connsp_2(C_24, A_18, B_22) | ~r1_tarski(B_22, k1_tops_1(A_18, C_24)) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.45  tff(c_449, plain, (![B_22]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_22) | ~r1_tarski(B_22, k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_437, c_34])).
% 2.61/1.45  tff(c_471, plain, (![B_95]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_95) | ~r1_tarski(B_95, k2_struct_0('#skF_3')) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_70, c_47, c_70, c_449])).
% 2.61/1.45  tff(c_474, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_471])).
% 2.61/1.45  tff(c_481, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_474])).
% 2.61/1.45  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_481])).
% 2.61/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.45  
% 2.61/1.45  Inference rules
% 2.61/1.45  ----------------------
% 2.61/1.45  #Ref     : 0
% 2.61/1.45  #Sup     : 89
% 2.61/1.45  #Fact    : 0
% 2.61/1.45  #Define  : 0
% 2.61/1.45  #Split   : 5
% 2.61/1.45  #Chain   : 0
% 2.61/1.45  #Close   : 0
% 2.61/1.45  
% 2.61/1.45  Ordering : KBO
% 2.61/1.45  
% 2.61/1.45  Simplification rules
% 2.61/1.45  ----------------------
% 2.61/1.45  #Subsume      : 6
% 2.61/1.45  #Demod        : 65
% 2.61/1.45  #Tautology    : 28
% 2.61/1.45  #SimpNegUnit  : 1
% 2.61/1.45  #BackRed      : 5
% 2.61/1.45  
% 2.61/1.45  #Partial instantiations: 0
% 2.61/1.45  #Strategies tried      : 1
% 2.61/1.45  
% 2.61/1.45  Timing (in seconds)
% 2.61/1.45  ----------------------
% 2.61/1.46  Preprocessing        : 0.32
% 2.61/1.46  Parsing              : 0.18
% 2.61/1.46  CNF conversion       : 0.02
% 2.61/1.46  Main loop            : 0.30
% 2.61/1.46  Inferencing          : 0.11
% 2.61/1.46  Reduction            : 0.09
% 2.61/1.46  Demodulation         : 0.06
% 2.61/1.46  BG Simplification    : 0.02
% 2.61/1.46  Subsumption          : 0.07
% 2.61/1.46  Abstraction          : 0.02
% 2.61/1.46  MUC search           : 0.00
% 2.61/1.46  Cooper               : 0.00
% 2.61/1.46  Total                : 0.66
% 2.61/1.46  Index Insertion      : 0.00
% 2.61/1.46  Index Deletion       : 0.00
% 2.61/1.46  Index Matching       : 0.00
% 2.61/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
