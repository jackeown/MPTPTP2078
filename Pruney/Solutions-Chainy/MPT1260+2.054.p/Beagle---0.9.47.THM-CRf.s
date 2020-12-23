%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:07 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.12s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 138 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 343 expanded)
%              Number of equality atoms :   44 (  86 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_93,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') != k2_tops_1('#skF_3','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_154,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    ! [C_40,A_28,D_42,B_36] :
      ( v3_pre_topc(C_40,A_28)
      | k1_tops_1(A_28,C_40) != C_40
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0(B_36)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5253,plain,(
    ! [D_271,B_272] :
      ( ~ m1_subset_1(D_271,k1_zfmisc_1(u1_struct_0(B_272)))
      | ~ l1_pre_topc(B_272) ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_5256,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_5253])).

tff(c_5260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5256])).

tff(c_5651,plain,(
    ! [C_286,A_287] :
      ( v3_pre_topc(C_286,A_287)
      | k1_tops_1(A_287,C_286) != C_286
      | ~ m1_subset_1(C_286,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5657,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_5651])).

tff(c_5661,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5657])).

tff(c_5662,plain,(
    k1_tops_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_5661])).

tff(c_473,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1(k2_pre_topc(A_89,B_90),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] :
      ( k7_subset_1(A_18,B_19,C_20) = k4_xboole_0(B_19,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6663,plain,(
    ! [A_312,B_313,C_314] :
      ( k7_subset_1(u1_struct_0(A_312),k2_pre_topc(A_312,B_313),C_314) = k4_xboole_0(k2_pre_topc(A_312,B_313),C_314)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ l1_pre_topc(A_312) ) ),
    inference(resolution,[status(thm)],[c_473,c_36])).

tff(c_6667,plain,(
    ! [C_314] :
      ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),C_314) = k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),C_314)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_6663])).

tff(c_6822,plain,(
    ! [C_317] : k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),C_317) = k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),C_317) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6667])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_246,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_62])).

tff(c_6832,plain,(
    k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6822,c_246])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_757,plain,(
    ! [A_109,B_110,C_111] :
      ( ~ r2_hidden('#skF_1'(A_109,B_110,C_111),C_111)
      | r2_hidden('#skF_2'(A_109,B_110,C_111),C_111)
      | k4_xboole_0(A_109,B_110) = C_111 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_766,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_757])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1762,plain,(
    ! [A_155,B_156,C_157] :
      ( ~ r2_hidden('#skF_1'(A_155,B_156,C_157),C_157)
      | r2_hidden('#skF_2'(A_155,B_156,C_157),B_156)
      | ~ r2_hidden('#skF_2'(A_155,B_156,C_157),A_155)
      | k4_xboole_0(A_155,B_156) = C_157 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5813,plain,(
    ! [A_294,B_295] :
      ( r2_hidden('#skF_2'(A_294,B_295,A_294),B_295)
      | ~ r2_hidden('#skF_2'(A_294,B_295,A_294),A_294)
      | k4_xboole_0(A_294,B_295) = A_294 ) ),
    inference(resolution,[status(thm)],[c_14,c_1762])).

tff(c_5854,plain,(
    ! [A_296,B_297] :
      ( r2_hidden('#skF_2'(A_296,B_297,A_296),B_297)
      | k4_xboole_0(A_296,B_297) = A_296 ) ),
    inference(resolution,[status(thm)],[c_766,c_5813])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6144,plain,(
    ! [A_303,A_304,B_305] :
      ( ~ r2_hidden('#skF_2'(A_303,k4_xboole_0(A_304,B_305),A_303),B_305)
      | k4_xboole_0(A_303,k4_xboole_0(A_304,B_305)) = A_303 ) ),
    inference(resolution,[status(thm)],[c_5854,c_6])).

tff(c_6231,plain,(
    ! [A_3,A_304] : k4_xboole_0(A_3,k4_xboole_0(A_304,A_3)) = A_3 ),
    inference(resolution,[status(thm)],[c_766,c_6144])).

tff(c_6861,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6832,c_6231])).

tff(c_376,plain,(
    ! [A_73,B_74,C_75] :
      ( k7_subset_1(A_73,B_74,C_75) = k4_xboole_0(B_74,C_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_379,plain,(
    ! [C_75] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_75) = k4_xboole_0('#skF_4',C_75) ),
    inference(resolution,[status(thm)],[c_50,c_376])).

tff(c_939,plain,(
    ! [A_120,B_121] :
      ( k7_subset_1(u1_struct_0(A_120),B_121,k2_tops_1(A_120,B_121)) = k1_tops_1(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_943,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_939])).

tff(c_947,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_379,c_943])).

tff(c_6920,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6861,c_947])).

tff(c_6922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5662,c_6920])).

tff(c_6923,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') != k2_tops_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6924,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_46,plain,(
    ! [B_36,D_42,C_40,A_28] :
      ( k1_tops_1(B_36,D_42) = D_42
      | ~ v3_pre_topc(D_42,B_36)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0(B_36)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9942,plain,(
    ! [C_471,A_472] :
      ( ~ m1_subset_1(C_471,k1_zfmisc_1(u1_struct_0(A_472)))
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472) ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_9948,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_9942])).

tff(c_9953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_9948])).

tff(c_10295,plain,(
    ! [B_482,D_483] :
      ( k1_tops_1(B_482,D_483) = D_483
      | ~ v3_pre_topc(D_483,B_482)
      | ~ m1_subset_1(D_483,k1_zfmisc_1(u1_struct_0(B_482)))
      | ~ l1_pre_topc(B_482) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_10301,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_10295])).

tff(c_10305,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6924,c_10301])).

tff(c_42,plain,(
    ! [A_25,B_27] :
      ( k7_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_27),k1_tops_1(A_25,B_27)) = k2_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10326,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10305,c_42])).

tff(c_10330,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_10326])).

tff(c_10332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6923,c_10330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.00/2.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.00/2.68  
% 8.00/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/2.68  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 8.12/2.68  
% 8.12/2.68  %Foreground sorts:
% 8.12/2.68  
% 8.12/2.68  
% 8.12/2.68  %Background operators:
% 8.12/2.68  
% 8.12/2.68  
% 8.12/2.68  %Foreground operators:
% 8.12/2.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.12/2.68  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.12/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.12/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.12/2.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.12/2.68  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.12/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.12/2.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.12/2.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.12/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.12/2.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.12/2.68  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.12/2.68  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.12/2.68  tff('#skF_3', type, '#skF_3': $i).
% 8.12/2.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.12/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.12/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.12/2.68  tff('#skF_4', type, '#skF_4': $i).
% 8.12/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.12/2.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.12/2.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.12/2.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.12/2.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.12/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.12/2.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.12/2.68  
% 8.12/2.70  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 8.12/2.70  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 8.12/2.70  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.12/2.70  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.12/2.70  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.12/2.70  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 8.12/2.70  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 8.12/2.70  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')!=k2_tops_1('#skF_3', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.12/2.70  tff(c_154, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 8.12/2.70  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.12/2.70  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.12/2.70  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.12/2.70  tff(c_44, plain, (![C_40, A_28, D_42, B_36]: (v3_pre_topc(C_40, A_28) | k1_tops_1(A_28, C_40)!=C_40 | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(B_36))) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.12/2.70  tff(c_5253, plain, (![D_271, B_272]: (~m1_subset_1(D_271, k1_zfmisc_1(u1_struct_0(B_272))) | ~l1_pre_topc(B_272))), inference(splitLeft, [status(thm)], [c_44])).
% 8.12/2.70  tff(c_5256, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_5253])).
% 8.12/2.70  tff(c_5260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_5256])).
% 8.12/2.70  tff(c_5651, plain, (![C_286, A_287]: (v3_pre_topc(C_286, A_287) | k1_tops_1(A_287, C_286)!=C_286 | ~m1_subset_1(C_286, k1_zfmisc_1(u1_struct_0(A_287))) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287))), inference(splitRight, [status(thm)], [c_44])).
% 8.12/2.70  tff(c_5657, plain, (v3_pre_topc('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_5651])).
% 8.12/2.70  tff(c_5661, plain, (v3_pre_topc('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5657])).
% 8.12/2.70  tff(c_5662, plain, (k1_tops_1('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_154, c_5661])).
% 8.12/2.70  tff(c_473, plain, (![A_89, B_90]: (m1_subset_1(k2_pre_topc(A_89, B_90), k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.12/2.70  tff(c_36, plain, (![A_18, B_19, C_20]: (k7_subset_1(A_18, B_19, C_20)=k4_xboole_0(B_19, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.12/2.70  tff(c_6663, plain, (![A_312, B_313, C_314]: (k7_subset_1(u1_struct_0(A_312), k2_pre_topc(A_312, B_313), C_314)=k4_xboole_0(k2_pre_topc(A_312, B_313), C_314) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_312))) | ~l1_pre_topc(A_312))), inference(resolution, [status(thm)], [c_473, c_36])).
% 8.12/2.70  tff(c_6667, plain, (![C_314]: (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), C_314)=k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), C_314) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_6663])).
% 8.12/2.70  tff(c_6822, plain, (![C_317]: (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), C_317)=k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), C_317))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6667])).
% 8.12/2.70  tff(c_62, plain, (v3_pre_topc('#skF_4', '#skF_3') | k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.12/2.70  tff(c_246, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_154, c_62])).
% 8.12/2.70  tff(c_6832, plain, (k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6822, c_246])).
% 8.12/2.70  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.12/2.70  tff(c_757, plain, (![A_109, B_110, C_111]: (~r2_hidden('#skF_1'(A_109, B_110, C_111), C_111) | r2_hidden('#skF_2'(A_109, B_110, C_111), C_111) | k4_xboole_0(A_109, B_110)=C_111)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.12/2.70  tff(c_766, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_757])).
% 8.12/2.70  tff(c_14, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.12/2.70  tff(c_1762, plain, (![A_155, B_156, C_157]: (~r2_hidden('#skF_1'(A_155, B_156, C_157), C_157) | r2_hidden('#skF_2'(A_155, B_156, C_157), B_156) | ~r2_hidden('#skF_2'(A_155, B_156, C_157), A_155) | k4_xboole_0(A_155, B_156)=C_157)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.12/2.70  tff(c_5813, plain, (![A_294, B_295]: (r2_hidden('#skF_2'(A_294, B_295, A_294), B_295) | ~r2_hidden('#skF_2'(A_294, B_295, A_294), A_294) | k4_xboole_0(A_294, B_295)=A_294)), inference(resolution, [status(thm)], [c_14, c_1762])).
% 8.12/2.70  tff(c_5854, plain, (![A_296, B_297]: (r2_hidden('#skF_2'(A_296, B_297, A_296), B_297) | k4_xboole_0(A_296, B_297)=A_296)), inference(resolution, [status(thm)], [c_766, c_5813])).
% 8.12/2.70  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.12/2.70  tff(c_6144, plain, (![A_303, A_304, B_305]: (~r2_hidden('#skF_2'(A_303, k4_xboole_0(A_304, B_305), A_303), B_305) | k4_xboole_0(A_303, k4_xboole_0(A_304, B_305))=A_303)), inference(resolution, [status(thm)], [c_5854, c_6])).
% 8.12/2.70  tff(c_6231, plain, (![A_3, A_304]: (k4_xboole_0(A_3, k4_xboole_0(A_304, A_3))=A_3)), inference(resolution, [status(thm)], [c_766, c_6144])).
% 8.12/2.70  tff(c_6861, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6832, c_6231])).
% 8.12/2.70  tff(c_376, plain, (![A_73, B_74, C_75]: (k7_subset_1(A_73, B_74, C_75)=k4_xboole_0(B_74, C_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.12/2.70  tff(c_379, plain, (![C_75]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_75)=k4_xboole_0('#skF_4', C_75))), inference(resolution, [status(thm)], [c_50, c_376])).
% 8.12/2.70  tff(c_939, plain, (![A_120, B_121]: (k7_subset_1(u1_struct_0(A_120), B_121, k2_tops_1(A_120, B_121))=k1_tops_1(A_120, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.12/2.70  tff(c_943, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_939])).
% 8.12/2.70  tff(c_947, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_379, c_943])).
% 8.12/2.70  tff(c_6920, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6861, c_947])).
% 8.12/2.70  tff(c_6922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5662, c_6920])).
% 8.12/2.70  tff(c_6923, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')!=k2_tops_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 8.12/2.70  tff(c_6924, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 8.12/2.70  tff(c_46, plain, (![B_36, D_42, C_40, A_28]: (k1_tops_1(B_36, D_42)=D_42 | ~v3_pre_topc(D_42, B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(B_36))) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.12/2.70  tff(c_9942, plain, (![C_471, A_472]: (~m1_subset_1(C_471, k1_zfmisc_1(u1_struct_0(A_472))) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472))), inference(splitLeft, [status(thm)], [c_46])).
% 8.12/2.70  tff(c_9948, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_9942])).
% 8.12/2.70  tff(c_9953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_9948])).
% 8.12/2.70  tff(c_10295, plain, (![B_482, D_483]: (k1_tops_1(B_482, D_483)=D_483 | ~v3_pre_topc(D_483, B_482) | ~m1_subset_1(D_483, k1_zfmisc_1(u1_struct_0(B_482))) | ~l1_pre_topc(B_482))), inference(splitRight, [status(thm)], [c_46])).
% 8.12/2.70  tff(c_10301, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_10295])).
% 8.12/2.70  tff(c_10305, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6924, c_10301])).
% 8.12/2.70  tff(c_42, plain, (![A_25, B_27]: (k7_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, B_27), k1_tops_1(A_25, B_27))=k2_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.12/2.70  tff(c_10326, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10305, c_42])).
% 8.12/2.70  tff(c_10330, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_10326])).
% 8.12/2.70  tff(c_10332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6923, c_10330])).
% 8.12/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/2.70  
% 8.12/2.70  Inference rules
% 8.12/2.70  ----------------------
% 8.12/2.70  #Ref     : 0
% 8.12/2.70  #Sup     : 2377
% 8.12/2.70  #Fact    : 0
% 8.12/2.70  #Define  : 0
% 8.12/2.70  #Split   : 12
% 8.12/2.70  #Chain   : 0
% 8.12/2.70  #Close   : 0
% 8.12/2.70  
% 8.12/2.70  Ordering : KBO
% 8.12/2.70  
% 8.12/2.70  Simplification rules
% 8.12/2.70  ----------------------
% 8.12/2.70  #Subsume      : 338
% 8.12/2.70  #Demod        : 1730
% 8.12/2.70  #Tautology    : 912
% 8.12/2.70  #SimpNegUnit  : 24
% 8.12/2.70  #BackRed      : 112
% 8.12/2.70  
% 8.12/2.70  #Partial instantiations: 0
% 8.12/2.70  #Strategies tried      : 1
% 8.12/2.70  
% 8.12/2.70  Timing (in seconds)
% 8.12/2.70  ----------------------
% 8.12/2.70  Preprocessing        : 0.35
% 8.12/2.70  Parsing              : 0.18
% 8.12/2.70  CNF conversion       : 0.03
% 8.12/2.70  Main loop            : 1.58
% 8.12/2.70  Inferencing          : 0.47
% 8.12/2.70  Reduction            : 0.63
% 8.12/2.70  Demodulation         : 0.50
% 8.12/2.70  BG Simplification    : 0.06
% 8.12/2.70  Subsumption          : 0.30
% 8.12/2.70  Abstraction          : 0.08
% 8.12/2.70  MUC search           : 0.00
% 8.12/2.70  Cooper               : 0.00
% 8.12/2.70  Total                : 1.97
% 8.12/2.70  Index Insertion      : 0.00
% 8.12/2.70  Index Deletion       : 0.00
% 8.12/2.70  Index Matching       : 0.00
% 8.12/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
