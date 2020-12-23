%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:07 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
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

tff(c_130,plain,(
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

tff(c_5048,plain,(
    ! [D_273,B_274] :
      ( ~ m1_subset_1(D_273,k1_zfmisc_1(u1_struct_0(B_274)))
      | ~ l1_pre_topc(B_274) ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_5051,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_5048])).

tff(c_5055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5051])).

tff(c_5225,plain,(
    ! [C_281,A_282] :
      ( v3_pre_topc(C_281,A_282)
      | k1_tops_1(A_282,C_281) != C_281
      | ~ m1_subset_1(C_281,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5231,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_5225])).

tff(c_5235,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5231])).

tff(c_5236,plain,(
    k1_tops_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_5235])).

tff(c_462,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1(k2_pre_topc(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] :
      ( k7_subset_1(A_18,B_19,C_20) = k4_xboole_0(B_19,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5956,plain,(
    ! [A_307,B_308,C_309] :
      ( k7_subset_1(u1_struct_0(A_307),k2_pre_topc(A_307,B_308),C_309) = k4_xboole_0(k2_pre_topc(A_307,B_308),C_309)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ l1_pre_topc(A_307) ) ),
    inference(resolution,[status(thm)],[c_462,c_36])).

tff(c_5960,plain,(
    ! [C_309] :
      ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),C_309) = k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),C_309)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_5956])).

tff(c_5965,plain,(
    ! [C_310] : k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),C_310) = k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),C_310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5960])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_230,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_62])).

tff(c_5975,plain,(
    k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5965,c_230])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_768,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r2_hidden('#skF_1'(A_112,B_113,C_114),C_114)
      | r2_hidden('#skF_2'(A_112,B_113,C_114),C_114)
      | k4_xboole_0(A_112,B_113) = C_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_777,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_768])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1623,plain,(
    ! [A_149,B_150,C_151] :
      ( ~ r2_hidden('#skF_1'(A_149,B_150,C_151),C_151)
      | r2_hidden('#skF_2'(A_149,B_150,C_151),B_150)
      | ~ r2_hidden('#skF_2'(A_149,B_150,C_151),A_149)
      | k4_xboole_0(A_149,B_150) = C_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5700,plain,(
    ! [A_299,B_300] :
      ( r2_hidden('#skF_2'(A_299,B_300,A_299),B_300)
      | ~ r2_hidden('#skF_2'(A_299,B_300,A_299),A_299)
      | k4_xboole_0(A_299,B_300) = A_299 ) ),
    inference(resolution,[status(thm)],[c_14,c_1623])).

tff(c_5741,plain,(
    ! [A_301,B_302] :
      ( r2_hidden('#skF_2'(A_301,B_302,A_301),B_302)
      | k4_xboole_0(A_301,B_302) = A_301 ) ),
    inference(resolution,[status(thm)],[c_777,c_5700])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7306,plain,(
    ! [A_332,A_333,B_334] :
      ( ~ r2_hidden('#skF_2'(A_332,k4_xboole_0(A_333,B_334),A_332),B_334)
      | k4_xboole_0(A_332,k4_xboole_0(A_333,B_334)) = A_332 ) ),
    inference(resolution,[status(thm)],[c_5741,c_6])).

tff(c_7422,plain,(
    ! [A_335,A_336] : k4_xboole_0(A_335,k4_xboole_0(A_336,A_335)) = A_335 ),
    inference(resolution,[status(thm)],[c_777,c_7306])).

tff(c_7511,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5975,c_7422])).

tff(c_395,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_398,plain,(
    ! [C_88] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_88) = k4_xboole_0('#skF_4',C_88) ),
    inference(resolution,[status(thm)],[c_50,c_395])).

tff(c_946,plain,(
    ! [A_123,B_124] :
      ( k7_subset_1(u1_struct_0(A_123),B_124,k2_tops_1(A_123,B_124)) = k1_tops_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_950,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_946])).

tff(c_954,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_398,c_950])).

tff(c_7748,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7511,c_954])).

tff(c_7750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5236,c_7748])).

tff(c_7751,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') != k2_tops_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_7752,plain,(
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

tff(c_11740,plain,(
    ! [C_519,A_520] :
      ( ~ m1_subset_1(C_519,k1_zfmisc_1(u1_struct_0(A_520)))
      | ~ l1_pre_topc(A_520)
      | ~ v2_pre_topc(A_520) ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_11746,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_11740])).

tff(c_11751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_11746])).

tff(c_11753,plain,(
    ! [B_521,D_522] :
      ( k1_tops_1(B_521,D_522) = D_522
      | ~ v3_pre_topc(D_522,B_521)
      | ~ m1_subset_1(D_522,k1_zfmisc_1(u1_struct_0(B_521)))
      | ~ l1_pre_topc(B_521) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_11759,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_11753])).

tff(c_11763,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7752,c_11759])).

tff(c_42,plain,(
    ! [A_25,B_27] :
      ( k7_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_27),k1_tops_1(A_25,B_27)) = k2_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11785,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11763,c_42])).

tff(c_11789,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_11785])).

tff(c_11791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7751,c_11789])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.77  
% 7.68/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.77  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 7.68/2.77  
% 7.68/2.77  %Foreground sorts:
% 7.68/2.77  
% 7.68/2.77  
% 7.68/2.77  %Background operators:
% 7.68/2.77  
% 7.68/2.77  
% 7.68/2.77  %Foreground operators:
% 7.68/2.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.68/2.77  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.68/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.68/2.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.68/2.77  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.68/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.68/2.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.68/2.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.68/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.68/2.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.68/2.77  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.68/2.77  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.68/2.77  tff('#skF_3', type, '#skF_3': $i).
% 7.68/2.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.68/2.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.68/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.77  tff('#skF_4', type, '#skF_4': $i).
% 7.68/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.68/2.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.68/2.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.68/2.77  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.68/2.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.68/2.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.68/2.77  
% 7.68/2.78  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 7.68/2.78  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 7.68/2.78  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.68/2.78  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.68/2.78  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.68/2.78  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 7.68/2.78  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 7.68/2.78  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')!=k2_tops_1('#skF_3', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.68/2.78  tff(c_130, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 7.68/2.78  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.68/2.78  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.68/2.78  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.68/2.78  tff(c_44, plain, (![C_40, A_28, D_42, B_36]: (v3_pre_topc(C_40, A_28) | k1_tops_1(A_28, C_40)!=C_40 | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(B_36))) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.68/2.78  tff(c_5048, plain, (![D_273, B_274]: (~m1_subset_1(D_273, k1_zfmisc_1(u1_struct_0(B_274))) | ~l1_pre_topc(B_274))), inference(splitLeft, [status(thm)], [c_44])).
% 7.68/2.78  tff(c_5051, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_5048])).
% 7.68/2.78  tff(c_5055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_5051])).
% 7.68/2.79  tff(c_5225, plain, (![C_281, A_282]: (v3_pre_topc(C_281, A_282) | k1_tops_1(A_282, C_281)!=C_281 | ~m1_subset_1(C_281, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282))), inference(splitRight, [status(thm)], [c_44])).
% 7.68/2.79  tff(c_5231, plain, (v3_pre_topc('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_5225])).
% 7.68/2.79  tff(c_5235, plain, (v3_pre_topc('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5231])).
% 7.68/2.79  tff(c_5236, plain, (k1_tops_1('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_130, c_5235])).
% 7.68/2.79  tff(c_462, plain, (![A_93, B_94]: (m1_subset_1(k2_pre_topc(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.68/2.79  tff(c_36, plain, (![A_18, B_19, C_20]: (k7_subset_1(A_18, B_19, C_20)=k4_xboole_0(B_19, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.68/2.79  tff(c_5956, plain, (![A_307, B_308, C_309]: (k7_subset_1(u1_struct_0(A_307), k2_pre_topc(A_307, B_308), C_309)=k4_xboole_0(k2_pre_topc(A_307, B_308), C_309) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0(A_307))) | ~l1_pre_topc(A_307))), inference(resolution, [status(thm)], [c_462, c_36])).
% 7.68/2.79  tff(c_5960, plain, (![C_309]: (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), C_309)=k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), C_309) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_5956])).
% 7.68/2.79  tff(c_5965, plain, (![C_310]: (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), C_310)=k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), C_310))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5960])).
% 7.68/2.79  tff(c_62, plain, (v3_pre_topc('#skF_4', '#skF_3') | k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.68/2.79  tff(c_230, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_130, c_62])).
% 7.68/2.79  tff(c_5975, plain, (k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5965, c_230])).
% 7.68/2.79  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.79  tff(c_768, plain, (![A_112, B_113, C_114]: (~r2_hidden('#skF_1'(A_112, B_113, C_114), C_114) | r2_hidden('#skF_2'(A_112, B_113, C_114), C_114) | k4_xboole_0(A_112, B_113)=C_114)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.79  tff(c_777, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_768])).
% 7.68/2.79  tff(c_14, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.79  tff(c_1623, plain, (![A_149, B_150, C_151]: (~r2_hidden('#skF_1'(A_149, B_150, C_151), C_151) | r2_hidden('#skF_2'(A_149, B_150, C_151), B_150) | ~r2_hidden('#skF_2'(A_149, B_150, C_151), A_149) | k4_xboole_0(A_149, B_150)=C_151)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.79  tff(c_5700, plain, (![A_299, B_300]: (r2_hidden('#skF_2'(A_299, B_300, A_299), B_300) | ~r2_hidden('#skF_2'(A_299, B_300, A_299), A_299) | k4_xboole_0(A_299, B_300)=A_299)), inference(resolution, [status(thm)], [c_14, c_1623])).
% 7.68/2.79  tff(c_5741, plain, (![A_301, B_302]: (r2_hidden('#skF_2'(A_301, B_302, A_301), B_302) | k4_xboole_0(A_301, B_302)=A_301)), inference(resolution, [status(thm)], [c_777, c_5700])).
% 7.68/2.79  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.79  tff(c_7306, plain, (![A_332, A_333, B_334]: (~r2_hidden('#skF_2'(A_332, k4_xboole_0(A_333, B_334), A_332), B_334) | k4_xboole_0(A_332, k4_xboole_0(A_333, B_334))=A_332)), inference(resolution, [status(thm)], [c_5741, c_6])).
% 7.68/2.79  tff(c_7422, plain, (![A_335, A_336]: (k4_xboole_0(A_335, k4_xboole_0(A_336, A_335))=A_335)), inference(resolution, [status(thm)], [c_777, c_7306])).
% 7.68/2.79  tff(c_7511, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5975, c_7422])).
% 7.68/2.79  tff(c_395, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.68/2.79  tff(c_398, plain, (![C_88]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_88)=k4_xboole_0('#skF_4', C_88))), inference(resolution, [status(thm)], [c_50, c_395])).
% 7.68/2.79  tff(c_946, plain, (![A_123, B_124]: (k7_subset_1(u1_struct_0(A_123), B_124, k2_tops_1(A_123, B_124))=k1_tops_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.68/2.79  tff(c_950, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_946])).
% 7.68/2.79  tff(c_954, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_398, c_950])).
% 7.68/2.79  tff(c_7748, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7511, c_954])).
% 7.68/2.79  tff(c_7750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5236, c_7748])).
% 7.68/2.79  tff(c_7751, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')!=k2_tops_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 7.68/2.79  tff(c_7752, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 7.68/2.79  tff(c_46, plain, (![B_36, D_42, C_40, A_28]: (k1_tops_1(B_36, D_42)=D_42 | ~v3_pre_topc(D_42, B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(B_36))) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.68/2.79  tff(c_11740, plain, (![C_519, A_520]: (~m1_subset_1(C_519, k1_zfmisc_1(u1_struct_0(A_520))) | ~l1_pre_topc(A_520) | ~v2_pre_topc(A_520))), inference(splitLeft, [status(thm)], [c_46])).
% 7.68/2.79  tff(c_11746, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_11740])).
% 7.68/2.79  tff(c_11751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_11746])).
% 7.68/2.79  tff(c_11753, plain, (![B_521, D_522]: (k1_tops_1(B_521, D_522)=D_522 | ~v3_pre_topc(D_522, B_521) | ~m1_subset_1(D_522, k1_zfmisc_1(u1_struct_0(B_521))) | ~l1_pre_topc(B_521))), inference(splitRight, [status(thm)], [c_46])).
% 7.68/2.79  tff(c_11759, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_11753])).
% 7.68/2.79  tff(c_11763, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7752, c_11759])).
% 7.68/2.79  tff(c_42, plain, (![A_25, B_27]: (k7_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, B_27), k1_tops_1(A_25, B_27))=k2_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.68/2.79  tff(c_11785, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11763, c_42])).
% 7.68/2.79  tff(c_11789, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_11785])).
% 7.68/2.79  tff(c_11791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7751, c_11789])).
% 7.68/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.79  
% 7.68/2.79  Inference rules
% 7.68/2.79  ----------------------
% 7.68/2.79  #Ref     : 0
% 7.68/2.79  #Sup     : 2715
% 7.68/2.79  #Fact    : 0
% 7.68/2.79  #Define  : 0
% 7.68/2.79  #Split   : 12
% 7.68/2.79  #Chain   : 0
% 7.68/2.79  #Close   : 0
% 7.68/2.79  
% 7.68/2.79  Ordering : KBO
% 7.68/2.79  
% 7.68/2.79  Simplification rules
% 7.68/2.79  ----------------------
% 7.68/2.79  #Subsume      : 420
% 7.68/2.79  #Demod        : 1800
% 7.68/2.79  #Tautology    : 898
% 7.68/2.79  #SimpNegUnit  : 23
% 7.68/2.79  #BackRed      : 81
% 7.68/2.79  
% 7.68/2.79  #Partial instantiations: 0
% 7.68/2.79  #Strategies tried      : 1
% 7.68/2.79  
% 7.68/2.79  Timing (in seconds)
% 7.68/2.79  ----------------------
% 7.68/2.79  Preprocessing        : 0.32
% 7.68/2.79  Parsing              : 0.17
% 7.68/2.79  CNF conversion       : 0.02
% 7.68/2.79  Main loop            : 1.65
% 7.68/2.79  Inferencing          : 0.47
% 7.68/2.79  Reduction            : 0.66
% 7.68/2.79  Demodulation         : 0.54
% 7.68/2.79  BG Simplification    : 0.07
% 7.68/2.79  Subsumption          : 0.34
% 7.68/2.79  Abstraction          : 0.08
% 7.68/2.79  MUC search           : 0.00
% 7.68/2.79  Cooper               : 0.00
% 7.68/2.79  Total                : 2.00
% 7.68/2.79  Index Insertion      : 0.00
% 7.68/2.79  Index Deletion       : 0.00
% 7.68/2.79  Index Matching       : 0.00
% 7.68/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
