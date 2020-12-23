%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:16 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 398 expanded)
%              Number of leaves         :   35 ( 147 expanded)
%              Depth                    :   11
%              Number of atoms          :  266 (1167 expanded)
%              Number of equality atoms :    9 (  30 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m2_connsp_2(C,A,k6_domain_1(u1_struct_0(A),B))
                <=> m1_connsp_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_26,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3675,plain,(
    ! [C_437,B_438,A_439] :
      ( ~ v1_xboole_0(C_437)
      | ~ m1_subset_1(B_438,k1_zfmisc_1(C_437))
      | ~ r2_hidden(A_439,B_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3684,plain,(
    ! [A_439] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_439,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_3675])).

tff(c_3685,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3684])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3687,plain,(
    ! [A_442,B_443] :
      ( k6_domain_1(A_442,B_443) = k1_tarski(B_443)
      | ~ m1_subset_1(B_443,A_442)
      | v1_xboole_0(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3699,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_3687])).

tff(c_3705,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3685,c_3699])).

tff(c_72,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_70,plain,(
    ~ m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_104,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_60])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1078,plain,(
    ! [B_201,A_202,C_203] :
      ( r2_hidden(B_201,k1_tops_1(A_202,C_203))
      | ~ m1_connsp_2(C_203,A_202,B_201)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ m1_subset_1(B_201,u1_struct_0(A_202))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1114,plain,(
    ! [B_201,A_202,A_10] :
      ( r2_hidden(B_201,k1_tops_1(A_202,A_10))
      | ~ m1_connsp_2(A_10,A_202,B_201)
      | ~ m1_subset_1(B_201,u1_struct_0(A_202))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202)
      | ~ r1_tarski(A_10,u1_struct_0(A_202)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1078])).

tff(c_93,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_103,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k1_tarski(A_57),k1_zfmisc_1(B_58))
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k1_tarski(A_57),B_58)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_81,c_18])).

tff(c_957,plain,(
    ! [C_186,A_187,B_188] :
      ( m2_connsp_2(C_186,A_187,B_188)
      | ~ r1_tarski(B_188,k1_tops_1(A_187,C_186))
      | ~ m1_subset_1(C_186,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3476,plain,(
    ! [C_419,A_420,A_421] :
      ( m2_connsp_2(C_419,A_420,k1_tarski(A_421))
      | ~ m1_subset_1(C_419,k1_zfmisc_1(u1_struct_0(A_420)))
      | ~ m1_subset_1(k1_tarski(A_421),k1_zfmisc_1(u1_struct_0(A_420)))
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420)
      | ~ r2_hidden(A_421,k1_tops_1(A_420,C_419)) ) ),
    inference(resolution,[status(thm)],[c_85,c_957])).

tff(c_3504,plain,(
    ! [A_421] :
      ( m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_421))
      | ~ m1_subset_1(k1_tarski(A_421),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r2_hidden(A_421,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_44,c_3476])).

tff(c_3519,plain,(
    ! [A_422] :
      ( m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_422))
      | ~ m1_subset_1(k1_tarski(A_422),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_422,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3504])).

tff(c_3529,plain,(
    ! [A_423] :
      ( m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_423))
      | ~ r2_hidden(A_423,k1_tops_1('#skF_3','#skF_5'))
      | ~ r2_hidden(A_423,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_3519])).

tff(c_127,plain,(
    ! [A_74,B_75] :
      ( k6_domain_1(A_74,B_75) = k1_tarski(B_75)
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_139,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_127])).

tff(c_145,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_139])).

tff(c_146,plain,(
    ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_70])).

tff(c_3554,plain,
    ( ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3529,c_146])).

tff(c_3555,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3554])).

tff(c_3571,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_3555])).

tff(c_3574,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3571])).

tff(c_3576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_3574])).

tff(c_3577,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3554])).

tff(c_3599,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1114,c_3577])).

tff(c_3608,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_50,c_48,c_46,c_104,c_3599])).

tff(c_3610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3608])).

tff(c_3612,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_28,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3621,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3612,c_28])).

tff(c_3624,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3621])).

tff(c_3645,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_3624])).

tff(c_3649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3645])).

tff(c_3650,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3653,plain,(
    m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_3650,c_60])).

tff(c_3706,plain,(
    m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3705,c_3653])).

tff(c_4431,plain,(
    ! [B_557,A_558,C_559] :
      ( r1_tarski(B_557,k1_tops_1(A_558,C_559))
      | ~ m2_connsp_2(C_559,A_558,B_557)
      | ~ m1_subset_1(C_559,k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ m1_subset_1(B_557,k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ l1_pre_topc(A_558)
      | ~ v2_pre_topc(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4453,plain,(
    ! [B_557] :
      ( r1_tarski(B_557,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_557)
      | ~ m1_subset_1(B_557,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_4431])).

tff(c_4466,plain,(
    ! [B_560] :
      ( r1_tarski(B_560,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_560)
      | ~ m1_subset_1(B_560,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4453])).

tff(c_4533,plain,(
    ! [A_562] :
      ( r1_tarski(k1_tarski(A_562),k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_562))
      | ~ r2_hidden(A_562,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_4466])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3732,plain,(
    ! [A_451,C_452,B_453] :
      ( m1_subset_1(A_451,C_452)
      | ~ m1_subset_1(B_453,k1_zfmisc_1(C_452))
      | ~ r2_hidden(A_451,B_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3753,plain,(
    ! [A_458,B_459,A_460] :
      ( m1_subset_1(A_458,B_459)
      | ~ r2_hidden(A_458,A_460)
      | ~ r1_tarski(A_460,B_459) ) ),
    inference(resolution,[status(thm)],[c_20,c_3732])).

tff(c_3759,plain,(
    ! [C_5,B_459] :
      ( m1_subset_1(C_5,B_459)
      | ~ r1_tarski(k1_tarski(C_5),B_459) ) ),
    inference(resolution,[status(thm)],[c_4,c_3753])).

tff(c_4559,plain,(
    ! [A_563] :
      ( m1_subset_1(A_563,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_563))
      | ~ r2_hidden(A_563,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4533,c_3759])).

tff(c_4563,plain,
    ( m1_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3706,c_4559])).

tff(c_4564,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4563])).

tff(c_4580,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_4564])).

tff(c_4583,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4580])).

tff(c_4585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3685,c_4583])).

tff(c_4586,plain,(
    m1_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4563])).

tff(c_4507,plain,(
    ! [A_561] :
      ( r1_tarski(A_561,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',A_561)
      | ~ r1_tarski(A_561,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_20,c_4466])).

tff(c_3711,plain,(
    ! [B_444,A_445,A_446] :
      ( ~ v1_xboole_0(B_444)
      | ~ r2_hidden(A_445,A_446)
      | ~ r1_tarski(A_446,B_444) ) ),
    inference(resolution,[status(thm)],[c_20,c_3675])).

tff(c_3717,plain,(
    ! [B_444,C_5] :
      ( ~ v1_xboole_0(B_444)
      | ~ r1_tarski(k1_tarski(C_5),B_444) ) ),
    inference(resolution,[status(thm)],[c_4,c_3711])).

tff(c_4531,plain,(
    ! [C_5] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(C_5))
      | ~ r1_tarski(k1_tarski(C_5),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4507,c_3717])).

tff(c_4532,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4531])).

tff(c_4856,plain,(
    ! [C_582,A_583,B_584] :
      ( m1_connsp_2(C_582,A_583,B_584)
      | ~ r2_hidden(B_584,k1_tops_1(A_583,C_582))
      | ~ m1_subset_1(C_582,k1_zfmisc_1(u1_struct_0(A_583)))
      | ~ m1_subset_1(B_584,u1_struct_0(A_583))
      | ~ l1_pre_topc(A_583)
      | ~ v2_pre_topc(A_583)
      | v2_struct_0(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5603,plain,(
    ! [C_662,A_663,A_664] :
      ( m1_connsp_2(C_662,A_663,A_664)
      | ~ m1_subset_1(C_662,k1_zfmisc_1(u1_struct_0(A_663)))
      | ~ m1_subset_1(A_664,u1_struct_0(A_663))
      | ~ l1_pre_topc(A_663)
      | ~ v2_pre_topc(A_663)
      | v2_struct_0(A_663)
      | v1_xboole_0(k1_tops_1(A_663,C_662))
      | ~ m1_subset_1(A_664,k1_tops_1(A_663,C_662)) ) ),
    inference(resolution,[status(thm)],[c_16,c_4856])).

tff(c_5628,plain,(
    ! [A_664] :
      ( m1_connsp_2('#skF_5','#skF_3',A_664)
      | ~ m1_subset_1(A_664,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(A_664,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_44,c_5603])).

tff(c_5642,plain,(
    ! [A_664] :
      ( m1_connsp_2('#skF_5','#skF_3',A_664)
      | ~ m1_subset_1(A_664,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(A_664,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_5628])).

tff(c_5644,plain,(
    ! [A_665] :
      ( m1_connsp_2('#skF_5','#skF_3',A_665)
      | ~ m1_subset_1(A_665,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_665,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4532,c_52,c_5642])).

tff(c_5651,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4586,c_5644])).

tff(c_5671,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5651])).

tff(c_5673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3650,c_5671])).

tff(c_5675,plain,(
    v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4531])).

tff(c_5685,plain,(
    ! [A_667] :
      ( r1_tarski(k1_tarski(A_667),k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_667))
      | ~ r2_hidden(A_667,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_4466])).

tff(c_5699,plain,(
    ! [A_667] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_667))
      | ~ r2_hidden(A_667,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5685,c_3717])).

tff(c_5717,plain,(
    ! [A_668] :
      ( ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_668))
      | ~ r2_hidden(A_668,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5675,c_5699])).

tff(c_5721,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3706,c_5717])).

tff(c_5724,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_5721])).

tff(c_5727,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5724])).

tff(c_5729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3685,c_5727])).

tff(c_5731,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3684])).

tff(c_5740,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5731,c_28])).

tff(c_5743,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5740])).

tff(c_5746,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_5743])).

tff(c_5750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.71/2.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.60  
% 7.71/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.60  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.71/2.60  
% 7.71/2.60  %Foreground sorts:
% 7.71/2.60  
% 7.71/2.60  
% 7.71/2.60  %Background operators:
% 7.71/2.60  
% 7.71/2.60  
% 7.71/2.60  %Foreground operators:
% 7.71/2.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.71/2.60  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.71/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.71/2.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.71/2.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.71/2.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.71/2.60  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.71/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.71/2.60  tff('#skF_5', type, '#skF_5': $i).
% 7.71/2.60  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.71/2.60  tff('#skF_3', type, '#skF_3': $i).
% 7.71/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.71/2.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.71/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.71/2.60  tff('#skF_4', type, '#skF_4': $i).
% 7.71/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.71/2.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.71/2.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.71/2.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.71/2.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.71/2.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.71/2.60  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 7.71/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.71/2.60  
% 7.71/2.62  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 7.71/2.62  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.71/2.62  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.71/2.62  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.71/2.62  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.71/2.62  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.71/2.62  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 7.71/2.62  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 7.71/2.62  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 7.71/2.62  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.71/2.62  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.71/2.62  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.71/2.62  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.71/2.62  tff(c_26, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.71/2.62  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.71/2.62  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.71/2.62  tff(c_3675, plain, (![C_437, B_438, A_439]: (~v1_xboole_0(C_437) | ~m1_subset_1(B_438, k1_zfmisc_1(C_437)) | ~r2_hidden(A_439, B_438))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.71/2.62  tff(c_3684, plain, (![A_439]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_439, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_3675])).
% 7.71/2.62  tff(c_3685, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_3684])).
% 7.71/2.62  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.71/2.62  tff(c_16, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.71/2.62  tff(c_3687, plain, (![A_442, B_443]: (k6_domain_1(A_442, B_443)=k1_tarski(B_443) | ~m1_subset_1(B_443, A_442) | v1_xboole_0(A_442))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.71/2.62  tff(c_3699, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_3687])).
% 7.71/2.62  tff(c_3705, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3685, c_3699])).
% 7.71/2.62  tff(c_72, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.71/2.62  tff(c_80, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_72])).
% 7.71/2.62  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.71/2.62  tff(c_54, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.71/2.62  tff(c_70, plain, (~m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_54])).
% 7.71/2.62  tff(c_60, plain, (m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.71/2.62  tff(c_104, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_60])).
% 7.71/2.62  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.71/2.62  tff(c_1078, plain, (![B_201, A_202, C_203]: (r2_hidden(B_201, k1_tops_1(A_202, C_203)) | ~m1_connsp_2(C_203, A_202, B_201) | ~m1_subset_1(C_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~m1_subset_1(B_201, u1_struct_0(A_202)) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.71/2.62  tff(c_1114, plain, (![B_201, A_202, A_10]: (r2_hidden(B_201, k1_tops_1(A_202, A_10)) | ~m1_connsp_2(A_10, A_202, B_201) | ~m1_subset_1(B_201, u1_struct_0(A_202)) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202) | ~r1_tarski(A_10, u1_struct_0(A_202)))), inference(resolution, [status(thm)], [c_20, c_1078])).
% 7.71/2.62  tff(c_93, plain, (![C_63, B_64, A_65]: (~v1_xboole_0(C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.71/2.62  tff(c_102, plain, (![A_65]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_93])).
% 7.71/2.62  tff(c_103, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_102])).
% 7.71/2.62  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.71/2.62  tff(c_81, plain, (![A_57, B_58]: (m1_subset_1(k1_tarski(A_57), k1_zfmisc_1(B_58)) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.71/2.62  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.71/2.62  tff(c_85, plain, (![A_57, B_58]: (r1_tarski(k1_tarski(A_57), B_58) | ~r2_hidden(A_57, B_58))), inference(resolution, [status(thm)], [c_81, c_18])).
% 7.71/2.62  tff(c_957, plain, (![C_186, A_187, B_188]: (m2_connsp_2(C_186, A_187, B_188) | ~r1_tarski(B_188, k1_tops_1(A_187, C_186)) | ~m1_subset_1(C_186, k1_zfmisc_1(u1_struct_0(A_187))) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.71/2.62  tff(c_3476, plain, (![C_419, A_420, A_421]: (m2_connsp_2(C_419, A_420, k1_tarski(A_421)) | ~m1_subset_1(C_419, k1_zfmisc_1(u1_struct_0(A_420))) | ~m1_subset_1(k1_tarski(A_421), k1_zfmisc_1(u1_struct_0(A_420))) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420) | ~r2_hidden(A_421, k1_tops_1(A_420, C_419)))), inference(resolution, [status(thm)], [c_85, c_957])).
% 7.71/2.62  tff(c_3504, plain, (![A_421]: (m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_421)) | ~m1_subset_1(k1_tarski(A_421), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden(A_421, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_44, c_3476])).
% 7.71/2.62  tff(c_3519, plain, (![A_422]: (m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_422)) | ~m1_subset_1(k1_tarski(A_422), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_422, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3504])).
% 7.71/2.62  tff(c_3529, plain, (![A_423]: (m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_423)) | ~r2_hidden(A_423, k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden(A_423, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_3519])).
% 7.71/2.62  tff(c_127, plain, (![A_74, B_75]: (k6_domain_1(A_74, B_75)=k1_tarski(B_75) | ~m1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.71/2.62  tff(c_139, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_127])).
% 7.71/2.62  tff(c_145, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_103, c_139])).
% 7.71/2.62  tff(c_146, plain, (~m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_70])).
% 7.71/2.62  tff(c_3554, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3529, c_146])).
% 7.71/2.62  tff(c_3555, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_3554])).
% 7.71/2.62  tff(c_3571, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_3555])).
% 7.71/2.62  tff(c_3574, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3571])).
% 7.71/2.62  tff(c_3576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_3574])).
% 7.71/2.62  tff(c_3577, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_3554])).
% 7.71/2.62  tff(c_3599, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1114, c_3577])).
% 7.71/2.62  tff(c_3608, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_50, c_48, c_46, c_104, c_3599])).
% 7.71/2.62  tff(c_3610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3608])).
% 7.71/2.62  tff(c_3612, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_102])).
% 7.71/2.62  tff(c_28, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.71/2.62  tff(c_3621, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3612, c_28])).
% 7.71/2.62  tff(c_3624, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_3621])).
% 7.71/2.62  tff(c_3645, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_3624])).
% 7.71/2.62  tff(c_3649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3645])).
% 7.71/2.62  tff(c_3650, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 7.71/2.62  tff(c_3653, plain, (m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3650, c_60])).
% 7.71/2.62  tff(c_3706, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3705, c_3653])).
% 7.71/2.62  tff(c_4431, plain, (![B_557, A_558, C_559]: (r1_tarski(B_557, k1_tops_1(A_558, C_559)) | ~m2_connsp_2(C_559, A_558, B_557) | ~m1_subset_1(C_559, k1_zfmisc_1(u1_struct_0(A_558))) | ~m1_subset_1(B_557, k1_zfmisc_1(u1_struct_0(A_558))) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.71/2.62  tff(c_4453, plain, (![B_557]: (r1_tarski(B_557, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_557) | ~m1_subset_1(B_557, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_4431])).
% 7.71/2.62  tff(c_4466, plain, (![B_560]: (r1_tarski(B_560, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_560) | ~m1_subset_1(B_560, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4453])).
% 7.71/2.62  tff(c_4533, plain, (![A_562]: (r1_tarski(k1_tarski(A_562), k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_562)) | ~r2_hidden(A_562, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_4466])).
% 7.71/2.62  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.71/2.62  tff(c_3732, plain, (![A_451, C_452, B_453]: (m1_subset_1(A_451, C_452) | ~m1_subset_1(B_453, k1_zfmisc_1(C_452)) | ~r2_hidden(A_451, B_453))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.71/2.62  tff(c_3753, plain, (![A_458, B_459, A_460]: (m1_subset_1(A_458, B_459) | ~r2_hidden(A_458, A_460) | ~r1_tarski(A_460, B_459))), inference(resolution, [status(thm)], [c_20, c_3732])).
% 7.71/2.62  tff(c_3759, plain, (![C_5, B_459]: (m1_subset_1(C_5, B_459) | ~r1_tarski(k1_tarski(C_5), B_459))), inference(resolution, [status(thm)], [c_4, c_3753])).
% 7.71/2.62  tff(c_4559, plain, (![A_563]: (m1_subset_1(A_563, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_563)) | ~r2_hidden(A_563, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4533, c_3759])).
% 7.71/2.62  tff(c_4563, plain, (m1_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3706, c_4559])).
% 7.71/2.62  tff(c_4564, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_4563])).
% 7.71/2.62  tff(c_4580, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_4564])).
% 7.71/2.62  tff(c_4583, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4580])).
% 7.71/2.62  tff(c_4585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3685, c_4583])).
% 7.71/2.62  tff(c_4586, plain, (m1_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_4563])).
% 7.71/2.62  tff(c_4507, plain, (![A_561]: (r1_tarski(A_561, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', A_561) | ~r1_tarski(A_561, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_20, c_4466])).
% 7.71/2.62  tff(c_3711, plain, (![B_444, A_445, A_446]: (~v1_xboole_0(B_444) | ~r2_hidden(A_445, A_446) | ~r1_tarski(A_446, B_444))), inference(resolution, [status(thm)], [c_20, c_3675])).
% 7.71/2.62  tff(c_3717, plain, (![B_444, C_5]: (~v1_xboole_0(B_444) | ~r1_tarski(k1_tarski(C_5), B_444))), inference(resolution, [status(thm)], [c_4, c_3711])).
% 7.71/2.62  tff(c_4531, plain, (![C_5]: (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(C_5)) | ~r1_tarski(k1_tarski(C_5), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4507, c_3717])).
% 7.71/2.62  tff(c_4532, plain, (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_4531])).
% 7.71/2.62  tff(c_4856, plain, (![C_582, A_583, B_584]: (m1_connsp_2(C_582, A_583, B_584) | ~r2_hidden(B_584, k1_tops_1(A_583, C_582)) | ~m1_subset_1(C_582, k1_zfmisc_1(u1_struct_0(A_583))) | ~m1_subset_1(B_584, u1_struct_0(A_583)) | ~l1_pre_topc(A_583) | ~v2_pre_topc(A_583) | v2_struct_0(A_583))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.71/2.62  tff(c_5603, plain, (![C_662, A_663, A_664]: (m1_connsp_2(C_662, A_663, A_664) | ~m1_subset_1(C_662, k1_zfmisc_1(u1_struct_0(A_663))) | ~m1_subset_1(A_664, u1_struct_0(A_663)) | ~l1_pre_topc(A_663) | ~v2_pre_topc(A_663) | v2_struct_0(A_663) | v1_xboole_0(k1_tops_1(A_663, C_662)) | ~m1_subset_1(A_664, k1_tops_1(A_663, C_662)))), inference(resolution, [status(thm)], [c_16, c_4856])).
% 7.71/2.62  tff(c_5628, plain, (![A_664]: (m1_connsp_2('#skF_5', '#skF_3', A_664) | ~m1_subset_1(A_664, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(A_664, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_44, c_5603])).
% 7.71/2.62  tff(c_5642, plain, (![A_664]: (m1_connsp_2('#skF_5', '#skF_3', A_664) | ~m1_subset_1(A_664, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(A_664, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_5628])).
% 7.71/2.62  tff(c_5644, plain, (![A_665]: (m1_connsp_2('#skF_5', '#skF_3', A_665) | ~m1_subset_1(A_665, u1_struct_0('#skF_3')) | ~m1_subset_1(A_665, k1_tops_1('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_4532, c_52, c_5642])).
% 7.71/2.62  tff(c_5651, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4586, c_5644])).
% 7.71/2.62  tff(c_5671, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5651])).
% 7.71/2.62  tff(c_5673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3650, c_5671])).
% 7.71/2.62  tff(c_5675, plain, (v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_4531])).
% 7.71/2.62  tff(c_5685, plain, (![A_667]: (r1_tarski(k1_tarski(A_667), k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_667)) | ~r2_hidden(A_667, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_4466])).
% 7.71/2.62  tff(c_5699, plain, (![A_667]: (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_667)) | ~r2_hidden(A_667, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5685, c_3717])).
% 7.71/2.62  tff(c_5717, plain, (![A_668]: (~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_668)) | ~r2_hidden(A_668, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5675, c_5699])).
% 7.71/2.62  tff(c_5721, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3706, c_5717])).
% 7.71/2.62  tff(c_5724, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_5721])).
% 7.71/2.62  tff(c_5727, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5724])).
% 7.71/2.62  tff(c_5729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3685, c_5727])).
% 7.71/2.62  tff(c_5731, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_3684])).
% 7.71/2.62  tff(c_5740, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_5731, c_28])).
% 7.71/2.62  tff(c_5743, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_5740])).
% 7.71/2.62  tff(c_5746, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_5743])).
% 7.71/2.62  tff(c_5750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_5746])).
% 7.71/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.62  
% 7.71/2.62  Inference rules
% 7.71/2.62  ----------------------
% 7.71/2.62  #Ref     : 0
% 7.71/2.62  #Sup     : 1261
% 7.71/2.62  #Fact    : 0
% 7.71/2.62  #Define  : 0
% 7.71/2.62  #Split   : 24
% 7.71/2.62  #Chain   : 0
% 7.71/2.62  #Close   : 0
% 7.71/2.62  
% 7.71/2.62  Ordering : KBO
% 7.71/2.62  
% 7.71/2.62  Simplification rules
% 7.71/2.62  ----------------------
% 7.71/2.62  #Subsume      : 155
% 7.71/2.62  #Demod        : 260
% 7.71/2.62  #Tautology    : 285
% 7.71/2.62  #SimpNegUnit  : 174
% 7.71/2.62  #BackRed      : 2
% 7.71/2.62  
% 7.71/2.62  #Partial instantiations: 0
% 7.71/2.62  #Strategies tried      : 1
% 7.71/2.62  
% 7.71/2.62  Timing (in seconds)
% 7.71/2.62  ----------------------
% 7.71/2.62  Preprocessing        : 0.34
% 7.71/2.62  Parsing              : 0.18
% 7.71/2.62  CNF conversion       : 0.03
% 7.71/2.62  Main loop            : 1.46
% 7.71/2.62  Inferencing          : 0.47
% 7.71/2.62  Reduction            : 0.38
% 7.71/2.62  Demodulation         : 0.23
% 7.71/2.62  BG Simplification    : 0.06
% 7.71/2.62  Subsumption          : 0.43
% 7.71/2.62  Abstraction          : 0.09
% 7.71/2.62  MUC search           : 0.00
% 7.71/2.62  Cooper               : 0.00
% 7.71/2.62  Total                : 1.84
% 7.71/2.62  Index Insertion      : 0.00
% 7.71/2.62  Index Deletion       : 0.00
% 7.71/2.62  Index Matching       : 0.00
% 7.71/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
