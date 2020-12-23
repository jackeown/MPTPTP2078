%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:24 EST 2020

% Result     : Theorem 6.37s
% Output     : CNFRefutation 6.78s
% Verified   : 
% Statistics : Number of formulae       :  232 (2422 expanded)
%              Number of leaves         :   34 ( 868 expanded)
%              Depth                    :   17
%              Number of atoms          :  535 (7665 expanded)
%              Number of equality atoms :   36 (1269 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v1_borsuk_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                 => ( ( v1_borsuk_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_borsuk_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_95,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_20,plain,(
    ! [A_9] :
      ( v4_pre_topc(k2_struct_0(A_9),A_9)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_18,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_18,c_98])).

tff(c_116,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_104])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2900,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_46])).

tff(c_3079,plain,(
    ! [B_211,A_212] :
      ( v4_pre_topc(B_211,g1_pre_topc(u1_struct_0(A_212),u1_pre_topc(A_212)))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ v4_pre_topc(B_211,A_212)
      | ~ l1_pre_topc(A_212)
      | ~ v2_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3082,plain,(
    ! [B_211] :
      ( v4_pre_topc(B_211,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_211,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_3079])).

tff(c_3263,plain,(
    ! [B_222] :
      ( v4_pre_topc(B_222,'#skF_3')
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_222,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116,c_2900,c_3082])).

tff(c_3277,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_3263])).

tff(c_3278,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3277])).

tff(c_3301,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_3278])).

tff(c_3305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3301])).

tff(c_3307,plain,(
    v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3277])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_115,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_104])).

tff(c_3497,plain,(
    ! [B_236,A_237] :
      ( m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_237),u1_pre_topc(A_237)))))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ v4_pre_topc(B_236,A_237)
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3511,plain,(
    ! [B_236] :
      ( m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_236,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_3497])).

tff(c_3551,plain,(
    ! [B_239] :
      ( m1_subset_1(B_239,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_239,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116,c_115,c_2900,c_3511])).

tff(c_3562,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_3551])).

tff(c_3567,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3307,c_3562])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3571,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3567,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3594,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3571,c_2])).

tff(c_3595,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3594])).

tff(c_3613,plain,(
    ! [B_243,A_244] :
      ( v4_pre_topc(B_243,A_244)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_244),u1_pre_topc(A_244)))))
      | ~ v4_pre_topc(B_243,g1_pre_topc(u1_struct_0(A_244),u1_pre_topc(A_244)))
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3635,plain,(
    ! [B_243] :
      ( v4_pre_topc(B_243,'#skF_2')
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_243,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_3613])).

tff(c_3663,plain,(
    ! [B_245] :
      ( v4_pre_topc(B_245,'#skF_2')
      | ~ m1_subset_1(B_245,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_245,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2900,c_116,c_115,c_2900,c_3635])).

tff(c_3687,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_3663])).

tff(c_3688,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3687])).

tff(c_3691,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3688])).

tff(c_3695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3691])).

tff(c_3697,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3687])).

tff(c_3755,plain,(
    ! [B_249,A_250] :
      ( m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_250),u1_pre_topc(A_250)))))
      | ~ v4_pre_topc(B_249,g1_pre_topc(u1_struct_0(A_250),u1_pre_topc(A_250)))
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3777,plain,(
    ! [B_249] :
      ( m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_249,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_3755])).

tff(c_3832,plain,(
    ! [B_252] :
      ( m1_subset_1(B_252,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_252,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2900,c_116,c_115,c_2900,c_116,c_3777])).

tff(c_3845,plain,(
    ! [B_253] :
      ( r1_tarski(B_253,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_253,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_253,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3832,c_12])).

tff(c_3862,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_3845])).

tff(c_3871,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3697,c_3862])).

tff(c_3873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3595,c_3871])).

tff(c_3874,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3594])).

tff(c_3910,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3874,c_2900])).

tff(c_3911,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3874,c_116])).

tff(c_4312,plain,(
    ! [C_268,A_269] :
      ( m1_pre_topc(C_268,A_269)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_268),u1_pre_topc(C_268)),A_269)
      | ~ l1_pre_topc(C_268)
      | ~ v2_pre_topc(C_268)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_268),u1_pre_topc(C_268)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_268),u1_pre_topc(C_268)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4315,plain,(
    ! [A_269] :
      ( m1_pre_topc('#skF_2',A_269)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_269)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3911,c_4312])).

tff(c_4332,plain,(
    ! [A_270] :
      ( m1_pre_topc('#skF_2',A_270)
      | ~ m1_pre_topc('#skF_3',A_270)
      | ~ l1_pre_topc(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3910,c_3911,c_48,c_3910,c_3911,c_54,c_52,c_3910,c_4315])).

tff(c_74,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_97,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_60,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_118,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_95,c_60])).

tff(c_119,plain,(
    ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_124,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_46])).

tff(c_989,plain,(
    ! [C_101,A_102] :
      ( m1_pre_topc(C_101,A_102)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_101),u1_pre_topc(C_101)),A_102)
      | ~ l1_pre_topc(C_101)
      | ~ v2_pre_topc(C_101)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_101),u1_pre_topc(C_101)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_101),u1_pre_topc(C_101)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_998,plain,(
    ! [A_102] :
      ( m1_pre_topc('#skF_2',A_102)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_102)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_989])).

tff(c_1009,plain,(
    ! [A_103] :
      ( m1_pre_topc('#skF_2',A_103)
      | ~ m1_pre_topc('#skF_3',A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_124,c_116,c_48,c_124,c_116,c_54,c_52,c_124,c_998])).

tff(c_114,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_104])).

tff(c_162,plain,(
    ! [B_52,A_53] :
      ( m1_subset_1(u1_struct_0(B_52),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_183,plain,(
    ! [B_52] :
      ( m1_subset_1(u1_struct_0(B_52),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_52,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_162])).

tff(c_285,plain,(
    ! [B_63] :
      ( m1_subset_1(u1_struct_0(B_63),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_63,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_183])).

tff(c_309,plain,(
    ! [B_64] :
      ( r1_tarski(u1_struct_0(B_64),k2_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_64,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_285,c_12])).

tff(c_317,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_309])).

tff(c_325,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_1021,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1009,c_325])).

tff(c_1042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_95,c_1021])).

tff(c_1044,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_291,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_285])).

tff(c_300,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_291])).

tff(c_1067,plain,(
    ! [B_104,A_105] :
      ( v4_pre_topc(u1_struct_0(B_104),A_105)
      | ~ v1_borsuk_1(B_104,A_105)
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1091,plain,(
    ! [B_104] :
      ( v4_pre_topc(u1_struct_0(B_104),'#skF_1')
      | ~ v1_borsuk_1(B_104,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_104,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1067])).

tff(c_2854,plain,(
    ! [B_190] :
      ( v4_pre_topc(u1_struct_0(B_190),'#skF_1')
      | ~ v1_borsuk_1(B_190,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_190),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_190,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1091])).

tff(c_2866,plain,
    ( v4_pre_topc(u1_struct_0('#skF_3'),'#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2854])).

tff(c_2875,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_300,c_97,c_115,c_2866])).

tff(c_268,plain,(
    ! [B_61,A_62] :
      ( v4_pre_topc(B_61,g1_pre_topc(u1_struct_0(A_62),u1_pre_topc(A_62)))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ v4_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_274,plain,(
    ! [B_61] :
      ( v4_pre_topc(B_61,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_61,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_268])).

tff(c_1196,plain,(
    ! [B_111] :
      ( v4_pre_topc(B_111,'#skF_3')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_111,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116,c_124,c_274])).

tff(c_1210,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_1196])).

tff(c_1211,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1210])).

tff(c_1214,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1211])).

tff(c_1218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1214])).

tff(c_1220,plain,(
    v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1210])).

tff(c_1352,plain,(
    ! [B_120,A_121] :
      ( m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_121),u1_pre_topc(A_121)))))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v4_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1369,plain,(
    ! [B_120] :
      ( m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_120,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1352])).

tff(c_1511,plain,(
    ! [B_129] :
      ( m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_129,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116,c_115,c_124,c_1369])).

tff(c_1522,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_1511])).

tff(c_1527,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1522])).

tff(c_1531,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1527,c_12])).

tff(c_1584,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1531,c_2])).

tff(c_1585,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1584])).

tff(c_1532,plain,(
    ! [B_130,A_131] :
      ( v4_pre_topc(B_130,A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_131),u1_pre_topc(A_131)))))
      | ~ v4_pre_topc(B_130,g1_pre_topc(u1_struct_0(A_131),u1_pre_topc(A_131)))
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1561,plain,(
    ! [B_130] :
      ( v4_pre_topc(B_130,'#skF_2')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_130,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1532])).

tff(c_1586,plain,(
    ! [B_132] :
      ( v4_pre_topc(B_132,'#skF_2')
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_132,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_124,c_116,c_115,c_124,c_1561])).

tff(c_1606,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_1586])).

tff(c_1607,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1606])).

tff(c_1610,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1607])).

tff(c_1614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1610])).

tff(c_1616,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1606])).

tff(c_1635,plain,(
    ! [B_134,A_135] :
      ( m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)))))
      | ~ v4_pre_topc(B_134,g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1664,plain,(
    ! [B_134] :
      ( m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_134,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1635])).

tff(c_1713,plain,(
    ! [B_138] :
      ( m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_138,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_124,c_116,c_115,c_124,c_116,c_1664])).

tff(c_1738,plain,(
    ! [B_140] :
      ( r1_tarski(B_140,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_140,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1713,c_12])).

tff(c_1755,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_1738])).

tff(c_1764,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_1755])).

tff(c_1766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1585,c_1764])).

tff(c_1767,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1584])).

tff(c_1786,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_116])).

tff(c_44,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(u1_struct_0(B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1221,plain,(
    ! [B_112,A_113] :
      ( v1_borsuk_1(B_112,A_113)
      | ~ v4_pre_topc(u1_struct_0(B_112),A_113)
      | ~ m1_subset_1(u1_struct_0(B_112),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2165,plain,(
    ! [B_154,A_155] :
      ( v1_borsuk_1(B_154,A_155)
      | ~ v4_pre_topc(u1_struct_0(B_154),A_155)
      | ~ v2_pre_topc(A_155)
      | ~ m1_pre_topc(B_154,A_155)
      | ~ l1_pre_topc(A_155) ) ),
    inference(resolution,[status(thm)],[c_44,c_1221])).

tff(c_2171,plain,(
    ! [A_155] :
      ( v1_borsuk_1('#skF_2',A_155)
      | ~ v4_pre_topc(k2_struct_0('#skF_3'),A_155)
      | ~ v2_pre_topc(A_155)
      | ~ m1_pre_topc('#skF_2',A_155)
      | ~ l1_pre_topc(A_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_2165])).

tff(c_2880,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2875,c_2171])).

tff(c_2886,plain,(
    v1_borsuk_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1044,c_58,c_2880])).

tff(c_2888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_2886])).

tff(c_2889,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_4352,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4332,c_2889])).

tff(c_4371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_95,c_4352])).

tff(c_4373,plain,(
    ~ v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4372,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4375,plain,(
    ! [A_271] :
      ( u1_struct_0(A_271) = k2_struct_0(A_271)
      | ~ l1_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4380,plain,(
    ! [A_272] :
      ( u1_struct_0(A_272) = k2_struct_0(A_272)
      | ~ l1_pre_topc(A_272) ) ),
    inference(resolution,[status(thm)],[c_18,c_4375])).

tff(c_4391,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_4380])).

tff(c_4390,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_4380])).

tff(c_4431,plain,(
    ! [B_280,A_281] :
      ( m1_subset_1(u1_struct_0(B_280),k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ m1_pre_topc(B_280,A_281)
      | ~ l1_pre_topc(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4452,plain,(
    ! [B_280] :
      ( m1_subset_1(u1_struct_0(B_280),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_280,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4390,c_4431])).

tff(c_4554,plain,(
    ! [B_291] :
      ( m1_subset_1(u1_struct_0(B_291),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_291,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4452])).

tff(c_4563,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4391,c_4554])).

tff(c_4571,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4563])).

tff(c_76,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4374,plain,(
    v1_borsuk_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_4373,c_76])).

tff(c_4392,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_4380])).

tff(c_4401,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4392,c_46])).

tff(c_4587,plain,(
    ! [B_292,A_293] :
      ( v4_pre_topc(B_292,g1_pre_topc(u1_struct_0(A_293),u1_pre_topc(A_293)))
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ v4_pre_topc(B_292,A_293)
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4590,plain,(
    ! [B_292] :
      ( v4_pre_topc(B_292,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_292,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4392,c_4587])).

tff(c_4811,plain,(
    ! [B_305] :
      ( v4_pre_topc(B_305,'#skF_3')
      | ~ m1_subset_1(B_305,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_305,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4392,c_4401,c_4590])).

tff(c_4825,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_4811])).

tff(c_4826,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4825])).

tff(c_4829,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_4826])).

tff(c_4833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4829])).

tff(c_4835,plain,(
    v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4825])).

tff(c_4950,plain,(
    ! [B_314,A_315] :
      ( m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_315),u1_pre_topc(A_315)))))
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ v4_pre_topc(B_314,A_315)
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4964,plain,(
    ! [B_314] :
      ( m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_314,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4392,c_4950])).

tff(c_5066,plain,(
    ! [B_320] :
      ( m1_subset_1(B_320,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_320,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4392,c_4391,c_4401,c_4964])).

tff(c_5077,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_5066])).

tff(c_5082,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4835,c_5077])).

tff(c_5086,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5082,c_12])).

tff(c_5089,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5086,c_2])).

tff(c_5090,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5089])).

tff(c_5091,plain,(
    ! [B_321,A_322] :
      ( v4_pre_topc(B_321,A_322)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_322),u1_pre_topc(A_322)))))
      | ~ v4_pre_topc(B_321,g1_pre_topc(u1_struct_0(A_322),u1_pre_topc(A_322)))
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5117,plain,(
    ! [B_321] :
      ( v4_pre_topc(B_321,'#skF_2')
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_321,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4392,c_5091])).

tff(c_5141,plain,(
    ! [B_323] :
      ( v4_pre_topc(B_323,'#skF_2')
      | ~ m1_subset_1(B_323,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_323,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4401,c_4392,c_4391,c_4401,c_5117])).

tff(c_5161,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_5141])).

tff(c_5162,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5161])).

tff(c_5165,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_5162])).

tff(c_5169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_5165])).

tff(c_5171,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5161])).

tff(c_5229,plain,(
    ! [B_327,A_328] :
      ( m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_328),u1_pre_topc(A_328)))))
      | ~ v4_pre_topc(B_327,g1_pre_topc(u1_struct_0(A_328),u1_pre_topc(A_328)))
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5255,plain,(
    ! [B_327] :
      ( m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_327,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4392,c_5229])).

tff(c_5323,plain,(
    ! [B_332] :
      ( m1_subset_1(B_332,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_332,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_332,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4401,c_4392,c_4391,c_4401,c_4392,c_5255])).

tff(c_5336,plain,(
    ! [B_333] :
      ( r1_tarski(B_333,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_333,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_333,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5323,c_12])).

tff(c_5353,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_5336])).

tff(c_5362,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_5353])).

tff(c_5364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5090,c_5362])).

tff(c_5365,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5089])).

tff(c_5384,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5365,c_4392])).

tff(c_4836,plain,(
    ! [B_306,A_307] :
      ( v4_pre_topc(u1_struct_0(B_306),A_307)
      | ~ v1_borsuk_1(B_306,A_307)
      | ~ m1_subset_1(u1_struct_0(B_306),k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ m1_pre_topc(B_306,A_307)
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4860,plain,(
    ! [B_306] :
      ( v4_pre_topc(u1_struct_0(B_306),'#skF_1')
      | ~ v1_borsuk_1(B_306,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_306),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_306,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4390,c_4836])).

tff(c_6316,plain,(
    ! [B_377] :
      ( v4_pre_topc(u1_struct_0(B_377),'#skF_1')
      | ~ v1_borsuk_1(B_377,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_377),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_377,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4860])).

tff(c_6319,plain,
    ( v4_pre_topc(u1_struct_0('#skF_2'),'#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5384,c_6316])).

tff(c_6333,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4372,c_4571,c_4374,c_5384,c_6319])).

tff(c_4651,plain,(
    ! [B_297,A_298] :
      ( v1_borsuk_1(B_297,A_298)
      | ~ v4_pre_topc(u1_struct_0(B_297),A_298)
      | ~ m1_subset_1(u1_struct_0(B_297),k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ m1_pre_topc(B_297,A_298)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5995,plain,(
    ! [B_357,A_358] :
      ( v1_borsuk_1(B_357,A_358)
      | ~ v4_pre_topc(u1_struct_0(B_357),A_358)
      | ~ v2_pre_topc(A_358)
      | ~ m1_pre_topc(B_357,A_358)
      | ~ l1_pre_topc(A_358) ) ),
    inference(resolution,[status(thm)],[c_44,c_4651])).

tff(c_6011,plain,(
    ! [A_358] :
      ( v1_borsuk_1('#skF_3',A_358)
      | ~ v4_pre_topc(k2_struct_0('#skF_3'),A_358)
      | ~ v2_pre_topc(A_358)
      | ~ m1_pre_topc('#skF_3',A_358)
      | ~ l1_pre_topc(A_358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4391,c_5995])).

tff(c_6345,plain,
    ( v1_borsuk_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6333,c_6011])).

tff(c_6351,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_95,c_58,c_6345])).

tff(c_6353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4373,c_6351])).

tff(c_6355,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6354,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6361,plain,(
    ! [A_378] :
      ( u1_struct_0(A_378) = k2_struct_0(A_378)
      | ~ l1_struct_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6367,plain,(
    ! [A_379] :
      ( u1_struct_0(A_379) = k2_struct_0(A_379)
      | ~ l1_pre_topc(A_379) ) ),
    inference(resolution,[status(thm)],[c_18,c_6361])).

tff(c_6379,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_6367])).

tff(c_6388,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6379,c_46])).

tff(c_6482,plain,(
    ! [B_393,A_394] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_393),u1_pre_topc(B_393)),A_394)
      | ~ m1_pre_topc(B_393,A_394)
      | ~ l1_pre_topc(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6487,plain,(
    ! [A_394] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_394)
      | ~ m1_pre_topc('#skF_2',A_394)
      | ~ l1_pre_topc(A_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6379,c_6482])).

tff(c_6496,plain,(
    ! [A_395] :
      ( m1_pre_topc('#skF_3',A_395)
      | ~ m1_pre_topc('#skF_2',A_395)
      | ~ l1_pre_topc(A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6388,c_6487])).

tff(c_6499,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6354,c_6496])).

tff(c_6502,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6499])).

tff(c_6504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6355,c_6502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.37/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.38  
% 6.37/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.38  %$ v4_pre_topc > v1_borsuk_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.37/2.38  
% 6.37/2.38  %Foreground sorts:
% 6.37/2.38  
% 6.37/2.38  
% 6.37/2.38  %Background operators:
% 6.37/2.38  
% 6.37/2.38  
% 6.37/2.38  %Foreground operators:
% 6.37/2.38  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.37/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.37/2.38  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.37/2.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.37/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.37/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.37/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.37/2.38  tff('#skF_1', type, '#skF_1': $i).
% 6.37/2.38  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.37/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.37/2.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.37/2.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.37/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.37/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.37/2.38  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.37/2.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.37/2.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.37/2.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.37/2.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.37/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.37/2.38  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 6.37/2.38  
% 6.78/2.42  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> (v1_borsuk_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tmap_1)).
% 6.78/2.42  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 6.78/2.42  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.78/2.42  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.78/2.42  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.78/2.42  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.78/2.42  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v4_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v4_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_pre_topc)).
% 6.78/2.42  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.78/2.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.78/2.42  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 6.78/2.42  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.78/2.42  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tsep_1)).
% 6.78/2.42  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 6.78/2.42  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_68, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_95, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_68])).
% 6.78/2.42  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_20, plain, (![A_9]: (v4_pre_topc(k2_struct_0(A_9), A_9) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.78/2.42  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.78/2.42  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.78/2.42  tff(c_77, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 6.78/2.42  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.78/2.42  tff(c_98, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.78/2.42  tff(c_104, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_18, c_98])).
% 6.78/2.42  tff(c_116, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_104])).
% 6.78/2.42  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_2900, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_46])).
% 6.78/2.42  tff(c_3079, plain, (![B_211, A_212]: (v4_pre_topc(B_211, g1_pre_topc(u1_struct_0(A_212), u1_pre_topc(A_212))) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_212))) | ~v4_pre_topc(B_211, A_212) | ~l1_pre_topc(A_212) | ~v2_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_3082, plain, (![B_211]: (v4_pre_topc(B_211, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_211, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_3079])).
% 6.78/2.42  tff(c_3263, plain, (![B_222]: (v4_pre_topc(B_222, '#skF_3') | ~m1_subset_1(B_222, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_222, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116, c_2900, c_3082])).
% 6.78/2.42  tff(c_3277, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_3263])).
% 6.78/2.42  tff(c_3278, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3277])).
% 6.78/2.42  tff(c_3301, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_3278])).
% 6.78/2.42  tff(c_3305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3301])).
% 6.78/2.42  tff(c_3307, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_3277])).
% 6.78/2.42  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_115, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_104])).
% 6.78/2.42  tff(c_3497, plain, (![B_236, A_237]: (m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_237), u1_pre_topc(A_237))))) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(A_237))) | ~v4_pre_topc(B_236, A_237) | ~l1_pre_topc(A_237) | ~v2_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_3511, plain, (![B_236]: (m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_236, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_3497])).
% 6.78/2.42  tff(c_3551, plain, (![B_239]: (m1_subset_1(B_239, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_239, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_239, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116, c_115, c_2900, c_3511])).
% 6.78/2.42  tff(c_3562, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_3551])).
% 6.78/2.42  tff(c_3567, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3307, c_3562])).
% 6.78/2.42  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.78/2.42  tff(c_3571, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3567, c_12])).
% 6.78/2.42  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.78/2.42  tff(c_3594, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3571, c_2])).
% 6.78/2.42  tff(c_3595, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_3594])).
% 6.78/2.42  tff(c_3613, plain, (![B_243, A_244]: (v4_pre_topc(B_243, A_244) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_244), u1_pre_topc(A_244))))) | ~v4_pre_topc(B_243, g1_pre_topc(u1_struct_0(A_244), u1_pre_topc(A_244))) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_3635, plain, (![B_243]: (v4_pre_topc(B_243, '#skF_2') | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_243, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_3613])).
% 6.78/2.42  tff(c_3663, plain, (![B_245]: (v4_pre_topc(B_245, '#skF_2') | ~m1_subset_1(B_245, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_245, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2900, c_116, c_115, c_2900, c_3635])).
% 6.78/2.42  tff(c_3687, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_3663])).
% 6.78/2.42  tff(c_3688, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3687])).
% 6.78/2.42  tff(c_3691, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3688])).
% 6.78/2.42  tff(c_3695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3691])).
% 6.78/2.42  tff(c_3697, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_3687])).
% 6.78/2.42  tff(c_3755, plain, (![B_249, A_250]: (m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_250))) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_250), u1_pre_topc(A_250))))) | ~v4_pre_topc(B_249, g1_pre_topc(u1_struct_0(A_250), u1_pre_topc(A_250))) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_3777, plain, (![B_249]: (m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_249, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_3755])).
% 6.78/2.42  tff(c_3832, plain, (![B_252]: (m1_subset_1(B_252, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_252, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_252, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2900, c_116, c_115, c_2900, c_116, c_3777])).
% 6.78/2.42  tff(c_3845, plain, (![B_253]: (r1_tarski(B_253, k2_struct_0('#skF_2')) | ~m1_subset_1(B_253, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_253, '#skF_3'))), inference(resolution, [status(thm)], [c_3832, c_12])).
% 6.78/2.42  tff(c_3862, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_3845])).
% 6.78/2.42  tff(c_3871, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3697, c_3862])).
% 6.78/2.42  tff(c_3873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3595, c_3871])).
% 6.78/2.42  tff(c_3874, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_3594])).
% 6.78/2.42  tff(c_3910, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3874, c_2900])).
% 6.78/2.42  tff(c_3911, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3874, c_116])).
% 6.78/2.42  tff(c_4312, plain, (![C_268, A_269]: (m1_pre_topc(C_268, A_269) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_268), u1_pre_topc(C_268)), A_269) | ~l1_pre_topc(C_268) | ~v2_pre_topc(C_268) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_268), u1_pre_topc(C_268))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_268), u1_pre_topc(C_268))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.78/2.42  tff(c_4315, plain, (![A_269]: (m1_pre_topc('#skF_2', A_269) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_269) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_269))), inference(superposition, [status(thm), theory('equality')], [c_3911, c_4312])).
% 6.78/2.42  tff(c_4332, plain, (![A_270]: (m1_pre_topc('#skF_2', A_270) | ~m1_pre_topc('#skF_3', A_270) | ~l1_pre_topc(A_270))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3910, c_3911, c_48, c_3910, c_3911, c_54, c_52, c_3910, c_4315])).
% 6.78/2.42  tff(c_74, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_97, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_74])).
% 6.78/2.42  tff(c_60, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_118, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_95, c_60])).
% 6.78/2.42  tff(c_119, plain, (~v1_borsuk_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_118])).
% 6.78/2.42  tff(c_124, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_46])).
% 6.78/2.42  tff(c_989, plain, (![C_101, A_102]: (m1_pre_topc(C_101, A_102) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_101), u1_pre_topc(C_101)), A_102) | ~l1_pre_topc(C_101) | ~v2_pre_topc(C_101) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_101), u1_pre_topc(C_101))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_101), u1_pre_topc(C_101))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.78/2.42  tff(c_998, plain, (![A_102]: (m1_pre_topc('#skF_2', A_102) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_102) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_102))), inference(superposition, [status(thm), theory('equality')], [c_116, c_989])).
% 6.78/2.42  tff(c_1009, plain, (![A_103]: (m1_pre_topc('#skF_2', A_103) | ~m1_pre_topc('#skF_3', A_103) | ~l1_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_124, c_116, c_48, c_124, c_116, c_54, c_52, c_124, c_998])).
% 6.78/2.42  tff(c_114, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_104])).
% 6.78/2.42  tff(c_162, plain, (![B_52, A_53]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.78/2.42  tff(c_183, plain, (![B_52]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_52, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_162])).
% 6.78/2.42  tff(c_285, plain, (![B_63]: (m1_subset_1(u1_struct_0(B_63), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_63, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_183])).
% 6.78/2.42  tff(c_309, plain, (![B_64]: (r1_tarski(u1_struct_0(B_64), k2_struct_0('#skF_1')) | ~m1_pre_topc(B_64, '#skF_1'))), inference(resolution, [status(thm)], [c_285, c_12])).
% 6.78/2.42  tff(c_317, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_116, c_309])).
% 6.78/2.42  tff(c_325, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_317])).
% 6.78/2.42  tff(c_1021, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1009, c_325])).
% 6.78/2.42  tff(c_1042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_95, c_1021])).
% 6.78/2.42  tff(c_1044, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_317])).
% 6.78/2.42  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_291, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_115, c_285])).
% 6.78/2.42  tff(c_300, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_291])).
% 6.78/2.42  tff(c_1067, plain, (![B_104, A_105]: (v4_pre_topc(u1_struct_0(B_104), A_105) | ~v1_borsuk_1(B_104, A_105) | ~m1_subset_1(u1_struct_0(B_104), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.78/2.42  tff(c_1091, plain, (![B_104]: (v4_pre_topc(u1_struct_0(B_104), '#skF_1') | ~v1_borsuk_1(B_104, '#skF_1') | ~m1_subset_1(u1_struct_0(B_104), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_104, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_1067])).
% 6.78/2.42  tff(c_2854, plain, (![B_190]: (v4_pre_topc(u1_struct_0(B_190), '#skF_1') | ~v1_borsuk_1(B_190, '#skF_1') | ~m1_subset_1(u1_struct_0(B_190), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_190, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1091])).
% 6.78/2.42  tff(c_2866, plain, (v4_pre_topc(u1_struct_0('#skF_3'), '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_115, c_2854])).
% 6.78/2.42  tff(c_2875, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_300, c_97, c_115, c_2866])).
% 6.78/2.42  tff(c_268, plain, (![B_61, A_62]: (v4_pre_topc(B_61, g1_pre_topc(u1_struct_0(A_62), u1_pre_topc(A_62))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~v4_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_274, plain, (![B_61]: (v4_pre_topc(B_61, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_61, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_268])).
% 6.78/2.42  tff(c_1196, plain, (![B_111]: (v4_pre_topc(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_111, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116, c_124, c_274])).
% 6.78/2.42  tff(c_1210, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_1196])).
% 6.78/2.42  tff(c_1211, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1210])).
% 6.78/2.42  tff(c_1214, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1211])).
% 6.78/2.42  tff(c_1218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1214])).
% 6.78/2.42  tff(c_1220, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_1210])).
% 6.78/2.42  tff(c_1352, plain, (![B_120, A_121]: (m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_121), u1_pre_topc(A_121))))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~v4_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_1369, plain, (![B_120]: (m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_120, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1352])).
% 6.78/2.42  tff(c_1511, plain, (![B_129]: (m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_129, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116, c_115, c_124, c_1369])).
% 6.78/2.42  tff(c_1522, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_1511])).
% 6.78/2.42  tff(c_1527, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1522])).
% 6.78/2.42  tff(c_1531, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1527, c_12])).
% 6.78/2.42  tff(c_1584, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1531, c_2])).
% 6.78/2.42  tff(c_1585, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1584])).
% 6.78/2.42  tff(c_1532, plain, (![B_130, A_131]: (v4_pre_topc(B_130, A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_131), u1_pre_topc(A_131))))) | ~v4_pre_topc(B_130, g1_pre_topc(u1_struct_0(A_131), u1_pre_topc(A_131))) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_1561, plain, (![B_130]: (v4_pre_topc(B_130, '#skF_2') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_130, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1532])).
% 6.78/2.42  tff(c_1586, plain, (![B_132]: (v4_pre_topc(B_132, '#skF_2') | ~m1_subset_1(B_132, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_132, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_124, c_116, c_115, c_124, c_1561])).
% 6.78/2.42  tff(c_1606, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_1586])).
% 6.78/2.42  tff(c_1607, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1606])).
% 6.78/2.42  tff(c_1610, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1607])).
% 6.78/2.42  tff(c_1614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1610])).
% 6.78/2.42  tff(c_1616, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1606])).
% 6.78/2.42  tff(c_1635, plain, (![B_134, A_135]: (m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135))))) | ~v4_pre_topc(B_134, g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_1664, plain, (![B_134]: (m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_134, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1635])).
% 6.78/2.42  tff(c_1713, plain, (![B_138]: (m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_138, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_124, c_116, c_115, c_124, c_116, c_1664])).
% 6.78/2.42  tff(c_1738, plain, (![B_140]: (r1_tarski(B_140, k2_struct_0('#skF_2')) | ~m1_subset_1(B_140, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_140, '#skF_3'))), inference(resolution, [status(thm)], [c_1713, c_12])).
% 6.78/2.42  tff(c_1755, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_1738])).
% 6.78/2.42  tff(c_1764, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_1755])).
% 6.78/2.42  tff(c_1766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1585, c_1764])).
% 6.78/2.42  tff(c_1767, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1584])).
% 6.78/2.42  tff(c_1786, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_116])).
% 6.78/2.42  tff(c_44, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.78/2.42  tff(c_1221, plain, (![B_112, A_113]: (v1_borsuk_1(B_112, A_113) | ~v4_pre_topc(u1_struct_0(B_112), A_113) | ~m1_subset_1(u1_struct_0(B_112), k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.78/2.42  tff(c_2165, plain, (![B_154, A_155]: (v1_borsuk_1(B_154, A_155) | ~v4_pre_topc(u1_struct_0(B_154), A_155) | ~v2_pre_topc(A_155) | ~m1_pre_topc(B_154, A_155) | ~l1_pre_topc(A_155))), inference(resolution, [status(thm)], [c_44, c_1221])).
% 6.78/2.42  tff(c_2171, plain, (![A_155]: (v1_borsuk_1('#skF_2', A_155) | ~v4_pre_topc(k2_struct_0('#skF_3'), A_155) | ~v2_pre_topc(A_155) | ~m1_pre_topc('#skF_2', A_155) | ~l1_pre_topc(A_155))), inference(superposition, [status(thm), theory('equality')], [c_1786, c_2165])).
% 6.78/2.42  tff(c_2880, plain, (v1_borsuk_1('#skF_2', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2875, c_2171])).
% 6.78/2.42  tff(c_2886, plain, (v1_borsuk_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1044, c_58, c_2880])).
% 6.78/2.42  tff(c_2888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_2886])).
% 6.78/2.42  tff(c_2889, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_118])).
% 6.78/2.42  tff(c_4352, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4332, c_2889])).
% 6.78/2.42  tff(c_4371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_95, c_4352])).
% 6.78/2.42  tff(c_4373, plain, (~v1_borsuk_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_74])).
% 6.78/2.42  tff(c_4372, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_74])).
% 6.78/2.42  tff(c_4375, plain, (![A_271]: (u1_struct_0(A_271)=k2_struct_0(A_271) | ~l1_struct_0(A_271))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.78/2.42  tff(c_4380, plain, (![A_272]: (u1_struct_0(A_272)=k2_struct_0(A_272) | ~l1_pre_topc(A_272))), inference(resolution, [status(thm)], [c_18, c_4375])).
% 6.78/2.42  tff(c_4391, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_4380])).
% 6.78/2.42  tff(c_4390, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_4380])).
% 6.78/2.42  tff(c_4431, plain, (![B_280, A_281]: (m1_subset_1(u1_struct_0(B_280), k1_zfmisc_1(u1_struct_0(A_281))) | ~m1_pre_topc(B_280, A_281) | ~l1_pre_topc(A_281))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.78/2.42  tff(c_4452, plain, (![B_280]: (m1_subset_1(u1_struct_0(B_280), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_280, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4390, c_4431])).
% 6.78/2.42  tff(c_4554, plain, (![B_291]: (m1_subset_1(u1_struct_0(B_291), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_291, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4452])).
% 6.78/2.42  tff(c_4563, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4391, c_4554])).
% 6.78/2.42  tff(c_4571, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4563])).
% 6.78/2.42  tff(c_76, plain, (v1_borsuk_1('#skF_2', '#skF_1') | v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.78/2.42  tff(c_4374, plain, (v1_borsuk_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_4373, c_76])).
% 6.78/2.42  tff(c_4392, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_4380])).
% 6.78/2.42  tff(c_4401, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4392, c_46])).
% 6.78/2.42  tff(c_4587, plain, (![B_292, A_293]: (v4_pre_topc(B_292, g1_pre_topc(u1_struct_0(A_293), u1_pre_topc(A_293))) | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0(A_293))) | ~v4_pre_topc(B_292, A_293) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_4590, plain, (![B_292]: (v4_pre_topc(B_292, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_292, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4392, c_4587])).
% 6.78/2.42  tff(c_4811, plain, (![B_305]: (v4_pre_topc(B_305, '#skF_3') | ~m1_subset_1(B_305, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_305, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4392, c_4401, c_4590])).
% 6.78/2.42  tff(c_4825, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_4811])).
% 6.78/2.42  tff(c_4826, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_4825])).
% 6.78/2.42  tff(c_4829, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_4826])).
% 6.78/2.42  tff(c_4833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4829])).
% 6.78/2.42  tff(c_4835, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_4825])).
% 6.78/2.42  tff(c_4950, plain, (![B_314, A_315]: (m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_315), u1_pre_topc(A_315))))) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(A_315))) | ~v4_pre_topc(B_314, A_315) | ~l1_pre_topc(A_315) | ~v2_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_4964, plain, (![B_314]: (m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_314, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4392, c_4950])).
% 6.78/2.42  tff(c_5066, plain, (![B_320]: (m1_subset_1(B_320, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_320, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_320, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4392, c_4391, c_4401, c_4964])).
% 6.78/2.42  tff(c_5077, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_5066])).
% 6.78/2.42  tff(c_5082, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4835, c_5077])).
% 6.78/2.42  tff(c_5086, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_5082, c_12])).
% 6.78/2.42  tff(c_5089, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_5086, c_2])).
% 6.78/2.42  tff(c_5090, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_5089])).
% 6.78/2.42  tff(c_5091, plain, (![B_321, A_322]: (v4_pre_topc(B_321, A_322) | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_322), u1_pre_topc(A_322))))) | ~v4_pre_topc(B_321, g1_pre_topc(u1_struct_0(A_322), u1_pre_topc(A_322))) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_5117, plain, (![B_321]: (v4_pre_topc(B_321, '#skF_2') | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_321, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4392, c_5091])).
% 6.78/2.42  tff(c_5141, plain, (![B_323]: (v4_pre_topc(B_323, '#skF_2') | ~m1_subset_1(B_323, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_323, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4401, c_4392, c_4391, c_4401, c_5117])).
% 6.78/2.42  tff(c_5161, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_5141])).
% 6.78/2.42  tff(c_5162, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5161])).
% 6.78/2.42  tff(c_5165, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_5162])).
% 6.78/2.42  tff(c_5169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_5165])).
% 6.78/2.42  tff(c_5171, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_5161])).
% 6.78/2.42  tff(c_5229, plain, (![B_327, A_328]: (m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_328))) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_328), u1_pre_topc(A_328))))) | ~v4_pre_topc(B_327, g1_pre_topc(u1_struct_0(A_328), u1_pre_topc(A_328))) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.78/2.42  tff(c_5255, plain, (![B_327]: (m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_327, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4392, c_5229])).
% 6.78/2.42  tff(c_5323, plain, (![B_332]: (m1_subset_1(B_332, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_332, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_332, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4401, c_4392, c_4391, c_4401, c_4392, c_5255])).
% 6.78/2.42  tff(c_5336, plain, (![B_333]: (r1_tarski(B_333, k2_struct_0('#skF_2')) | ~m1_subset_1(B_333, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_333, '#skF_3'))), inference(resolution, [status(thm)], [c_5323, c_12])).
% 6.78/2.42  tff(c_5353, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_5336])).
% 6.78/2.42  tff(c_5362, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_5353])).
% 6.78/2.42  tff(c_5364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5090, c_5362])).
% 6.78/2.42  tff(c_5365, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5089])).
% 6.78/2.42  tff(c_5384, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5365, c_4392])).
% 6.78/2.42  tff(c_4836, plain, (![B_306, A_307]: (v4_pre_topc(u1_struct_0(B_306), A_307) | ~v1_borsuk_1(B_306, A_307) | ~m1_subset_1(u1_struct_0(B_306), k1_zfmisc_1(u1_struct_0(A_307))) | ~m1_pre_topc(B_306, A_307) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.78/2.42  tff(c_4860, plain, (![B_306]: (v4_pre_topc(u1_struct_0(B_306), '#skF_1') | ~v1_borsuk_1(B_306, '#skF_1') | ~m1_subset_1(u1_struct_0(B_306), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_306, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4390, c_4836])).
% 6.78/2.42  tff(c_6316, plain, (![B_377]: (v4_pre_topc(u1_struct_0(B_377), '#skF_1') | ~v1_borsuk_1(B_377, '#skF_1') | ~m1_subset_1(u1_struct_0(B_377), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_377, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4860])).
% 6.78/2.42  tff(c_6319, plain, (v4_pre_topc(u1_struct_0('#skF_2'), '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5384, c_6316])).
% 6.78/2.42  tff(c_6333, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4372, c_4571, c_4374, c_5384, c_6319])).
% 6.78/2.42  tff(c_4651, plain, (![B_297, A_298]: (v1_borsuk_1(B_297, A_298) | ~v4_pre_topc(u1_struct_0(B_297), A_298) | ~m1_subset_1(u1_struct_0(B_297), k1_zfmisc_1(u1_struct_0(A_298))) | ~m1_pre_topc(B_297, A_298) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.78/2.42  tff(c_5995, plain, (![B_357, A_358]: (v1_borsuk_1(B_357, A_358) | ~v4_pre_topc(u1_struct_0(B_357), A_358) | ~v2_pre_topc(A_358) | ~m1_pre_topc(B_357, A_358) | ~l1_pre_topc(A_358))), inference(resolution, [status(thm)], [c_44, c_4651])).
% 6.78/2.42  tff(c_6011, plain, (![A_358]: (v1_borsuk_1('#skF_3', A_358) | ~v4_pre_topc(k2_struct_0('#skF_3'), A_358) | ~v2_pre_topc(A_358) | ~m1_pre_topc('#skF_3', A_358) | ~l1_pre_topc(A_358))), inference(superposition, [status(thm), theory('equality')], [c_4391, c_5995])).
% 6.78/2.42  tff(c_6345, plain, (v1_borsuk_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6333, c_6011])).
% 6.78/2.42  tff(c_6351, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_95, c_58, c_6345])).
% 6.78/2.42  tff(c_6353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4373, c_6351])).
% 6.78/2.42  tff(c_6355, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 6.78/2.42  tff(c_6354, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 6.78/2.42  tff(c_6361, plain, (![A_378]: (u1_struct_0(A_378)=k2_struct_0(A_378) | ~l1_struct_0(A_378))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.78/2.42  tff(c_6367, plain, (![A_379]: (u1_struct_0(A_379)=k2_struct_0(A_379) | ~l1_pre_topc(A_379))), inference(resolution, [status(thm)], [c_18, c_6361])).
% 6.78/2.42  tff(c_6379, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_6367])).
% 6.78/2.42  tff(c_6388, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6379, c_46])).
% 6.78/2.42  tff(c_6482, plain, (![B_393, A_394]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_393), u1_pre_topc(B_393)), A_394) | ~m1_pre_topc(B_393, A_394) | ~l1_pre_topc(A_394))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.78/2.42  tff(c_6487, plain, (![A_394]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_394) | ~m1_pre_topc('#skF_2', A_394) | ~l1_pre_topc(A_394))), inference(superposition, [status(thm), theory('equality')], [c_6379, c_6482])).
% 6.78/2.42  tff(c_6496, plain, (![A_395]: (m1_pre_topc('#skF_3', A_395) | ~m1_pre_topc('#skF_2', A_395) | ~l1_pre_topc(A_395))), inference(demodulation, [status(thm), theory('equality')], [c_6388, c_6487])).
% 6.78/2.42  tff(c_6499, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6354, c_6496])).
% 6.78/2.42  tff(c_6502, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6499])).
% 6.78/2.42  tff(c_6504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6355, c_6502])).
% 6.78/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.78/2.42  
% 6.78/2.42  Inference rules
% 6.78/2.42  ----------------------
% 6.78/2.42  #Ref     : 0
% 6.78/2.42  #Sup     : 1311
% 6.78/2.42  #Fact    : 0
% 6.78/2.42  #Define  : 0
% 6.78/2.42  #Split   : 40
% 6.78/2.42  #Chain   : 0
% 6.78/2.42  #Close   : 0
% 6.78/2.42  
% 6.78/2.42  Ordering : KBO
% 6.78/2.42  
% 6.78/2.42  Simplification rules
% 6.78/2.42  ----------------------
% 6.78/2.42  #Subsume      : 428
% 6.78/2.42  #Demod        : 1571
% 6.78/2.42  #Tautology    : 316
% 6.78/2.42  #SimpNegUnit  : 22
% 6.78/2.42  #BackRed      : 53
% 6.78/2.42  
% 6.78/2.42  #Partial instantiations: 0
% 6.78/2.42  #Strategies tried      : 1
% 6.78/2.42  
% 6.78/2.42  Timing (in seconds)
% 6.78/2.42  ----------------------
% 6.78/2.42  Preprocessing        : 0.38
% 6.78/2.42  Parsing              : 0.20
% 6.78/2.42  CNF conversion       : 0.03
% 6.78/2.42  Main loop            : 1.15
% 6.78/2.42  Inferencing          : 0.39
% 6.78/2.42  Reduction            : 0.40
% 6.78/2.42  Demodulation         : 0.28
% 6.78/2.42  BG Simplification    : 0.04
% 6.78/2.42  Subsumption          : 0.23
% 6.78/2.42  Abstraction          : 0.05
% 6.78/2.42  MUC search           : 0.00
% 6.78/2.42  Cooper               : 0.00
% 6.78/2.42  Total                : 1.60
% 6.78/2.42  Index Insertion      : 0.00
% 6.78/2.42  Index Deletion       : 0.00
% 6.78/2.42  Index Matching       : 0.00
% 6.78/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
