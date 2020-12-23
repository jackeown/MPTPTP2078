%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:25 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :  233 (2323 expanded)
%              Number of leaves         :   35 ( 834 expanded)
%              Depth                    :   16
%              Number of atoms          :  536 (7362 expanded)
%              Number of equality atoms :   36 (1215 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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
                 => ( ( v1_tsep_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_tsep_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

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

tff(c_3156,plain,(
    ! [B_220,A_221] :
      ( v4_pre_topc(B_220,g1_pre_topc(u1_struct_0(A_221),u1_pre_topc(A_221)))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ v4_pre_topc(B_220,A_221)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3165,plain,(
    ! [B_220] :
      ( v4_pre_topc(B_220,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_220,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_3156])).

tff(c_3251,plain,(
    ! [B_226] :
      ( v4_pre_topc(B_226,'#skF_3')
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_226,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116,c_2900,c_3165])).

tff(c_3265,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_3251])).

tff(c_3266,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3265])).

tff(c_3269,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_3266])).

tff(c_3273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3269])).

tff(c_3275,plain,(
    v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3265])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_115,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_104])).

tff(c_3529,plain,(
    ! [B_242,A_243] :
      ( m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_243),u1_pre_topc(A_243)))))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ v4_pre_topc(B_242,A_243)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3549,plain,(
    ! [B_242] :
      ( m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_242,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_3529])).

tff(c_3559,plain,(
    ! [B_244] :
      ( m1_subset_1(B_244,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_244,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116,c_115,c_2900,c_3549])).

tff(c_3570,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_3559])).

tff(c_3575,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3275,c_3570])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3579,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3575,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3582,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3579,c_2])).

tff(c_3603,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3582])).

tff(c_3639,plain,(
    ! [B_249,A_250] :
      ( v4_pre_topc(B_249,A_250)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_250),u1_pre_topc(A_250)))))
      | ~ v4_pre_topc(B_249,g1_pre_topc(u1_struct_0(A_250),u1_pre_topc(A_250)))
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3671,plain,(
    ! [B_249] :
      ( v4_pre_topc(B_249,'#skF_2')
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_249,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_3639])).

tff(c_3689,plain,(
    ! [B_251] :
      ( v4_pre_topc(B_251,'#skF_2')
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_251,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2900,c_116,c_115,c_2900,c_3671])).

tff(c_3713,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_3689])).

tff(c_3714,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3713])).

tff(c_3717,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3714])).

tff(c_3721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3717])).

tff(c_3723,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3713])).

tff(c_3789,plain,(
    ! [B_255,A_256] :
      ( m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_256),u1_pre_topc(A_256)))))
      | ~ v4_pre_topc(B_255,g1_pre_topc(u1_struct_0(A_256),u1_pre_topc(A_256)))
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3821,plain,(
    ! [B_255] :
      ( m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_255,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_3789])).

tff(c_3839,plain,(
    ! [B_257] :
      ( m1_subset_1(B_257,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_257,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2900,c_116,c_115,c_2900,c_116,c_3821])).

tff(c_3852,plain,(
    ! [B_258] :
      ( r1_tarski(B_258,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_258,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_258,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3839,c_12])).

tff(c_3869,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_3852])).

tff(c_3878,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3723,c_3869])).

tff(c_3880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3603,c_3878])).

tff(c_3881,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3582])).

tff(c_3896,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_2900])).

tff(c_3897,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_116])).

tff(c_4337,plain,(
    ! [C_274,A_275] :
      ( m1_pre_topc(C_274,A_275)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_274),u1_pre_topc(C_274)),A_275)
      | ~ l1_pre_topc(C_274)
      | ~ v2_pre_topc(C_274)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_274),u1_pre_topc(C_274)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_274),u1_pre_topc(C_274)))
      | ~ l1_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4340,plain,(
    ! [A_275] :
      ( m1_pre_topc('#skF_2',A_275)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_275)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3897,c_4337])).

tff(c_4357,plain,(
    ! [A_276] :
      ( m1_pre_topc('#skF_2',A_276)
      | ~ m1_pre_topc('#skF_3',A_276)
      | ~ l1_pre_topc(A_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3896,c_3897,c_48,c_3896,c_3897,c_54,c_52,c_3896,c_4340])).

tff(c_74,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_97,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_60,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_118,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_95,c_60])).

tff(c_119,plain,(
    ~ v1_tsep_1('#skF_2','#skF_1') ),
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
    inference(cnfTransformation,[status(thm)],[f_93])).

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

tff(c_1221,plain,(
    ! [B_112,A_113] :
      ( v3_pre_topc(u1_struct_0(B_112),A_113)
      | ~ v1_tsep_1(B_112,A_113)
      | ~ m1_subset_1(u1_struct_0(B_112),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1245,plain,(
    ! [B_112] :
      ( v3_pre_topc(u1_struct_0(B_112),'#skF_1')
      | ~ v1_tsep_1(B_112,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_112),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_112,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1221])).

tff(c_2863,plain,(
    ! [B_195] :
      ( v3_pre_topc(u1_struct_0(B_195),'#skF_1')
      | ~ v1_tsep_1(B_195,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_195),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_195,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1245])).

tff(c_2875,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2863])).

tff(c_2884,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_300,c_97,c_115,c_2875])).

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

tff(c_1067,plain,(
    ! [B_104,A_105] :
      ( v1_tsep_1(B_104,A_105)
      | ~ v3_pre_topc(u1_struct_0(B_104),A_105)
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2345,plain,(
    ! [B_165,A_166] :
      ( v1_tsep_1(B_165,A_166)
      | ~ v3_pre_topc(u1_struct_0(B_165),A_166)
      | ~ v2_pre_topc(A_166)
      | ~ m1_pre_topc(B_165,A_166)
      | ~ l1_pre_topc(A_166) ) ),
    inference(resolution,[status(thm)],[c_44,c_1067])).

tff(c_2351,plain,(
    ! [A_166] :
      ( v1_tsep_1('#skF_2',A_166)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_166)
      | ~ v2_pre_topc(A_166)
      | ~ m1_pre_topc('#skF_2',A_166)
      | ~ l1_pre_topc(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_2345])).

tff(c_2889,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2884,c_2351])).

tff(c_2895,plain,(
    v1_tsep_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1044,c_58,c_2889])).

tff(c_2897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_2895])).

tff(c_2898,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_4377,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4357,c_2898])).

tff(c_4396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_95,c_4377])).

tff(c_4397,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4398,plain,(
    ~ v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_76,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4399,plain,(
    v1_tsep_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_4398,c_76])).

tff(c_4400,plain,(
    ! [A_277] :
      ( u1_struct_0(A_277) = k2_struct_0(A_277)
      | ~ l1_struct_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4405,plain,(
    ! [A_278] :
      ( u1_struct_0(A_278) = k2_struct_0(A_278)
      | ~ l1_pre_topc(A_278) ) ),
    inference(resolution,[status(thm)],[c_18,c_4400])).

tff(c_4417,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_4405])).

tff(c_4426,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4417,c_46])).

tff(c_4612,plain,(
    ! [B_298,A_299] :
      ( v4_pre_topc(B_298,g1_pre_topc(u1_struct_0(A_299),u1_pre_topc(A_299)))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ v4_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4615,plain,(
    ! [B_298] :
      ( v4_pre_topc(B_298,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_298,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4417,c_4612])).

tff(c_4836,plain,(
    ! [B_311] :
      ( v4_pre_topc(B_311,'#skF_3')
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_311,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4417,c_4426,c_4615])).

tff(c_4850,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_4836])).

tff(c_4851,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4850])).

tff(c_4854,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_4851])).

tff(c_4858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4854])).

tff(c_4860,plain,(
    v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4850])).

tff(c_4416,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_4405])).

tff(c_4975,plain,(
    ! [B_320,A_321] :
      ( m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_321),u1_pre_topc(A_321)))))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ v4_pre_topc(B_320,A_321)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4989,plain,(
    ! [B_320] :
      ( m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_320,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4417,c_4975])).

tff(c_5091,plain,(
    ! [B_326] :
      ( m1_subset_1(B_326,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_326,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v4_pre_topc(B_326,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4417,c_4416,c_4426,c_4989])).

tff(c_5102,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_5091])).

tff(c_5107,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4860,c_5102])).

tff(c_5111,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5107,c_12])).

tff(c_5114,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5111,c_2])).

tff(c_5115,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5114])).

tff(c_5116,plain,(
    ! [B_327,A_328] :
      ( v4_pre_topc(B_327,A_328)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_328),u1_pre_topc(A_328)))))
      | ~ v4_pre_topc(B_327,g1_pre_topc(u1_struct_0(A_328),u1_pre_topc(A_328)))
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5142,plain,(
    ! [B_327] :
      ( v4_pre_topc(B_327,'#skF_2')
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_327,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4417,c_5116])).

tff(c_5166,plain,(
    ! [B_329] :
      ( v4_pre_topc(B_329,'#skF_2')
      | ~ m1_subset_1(B_329,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_329,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4426,c_4417,c_4416,c_4426,c_5142])).

tff(c_5186,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_5166])).

tff(c_5187,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5186])).

tff(c_5190,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_5187])).

tff(c_5194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_5190])).

tff(c_5196,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5186])).

tff(c_5254,plain,(
    ! [B_333,A_334] :
      ( m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_334),u1_pre_topc(A_334)))))
      | ~ v4_pre_topc(B_333,g1_pre_topc(u1_struct_0(A_334),u1_pre_topc(A_334)))
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5280,plain,(
    ! [B_333] :
      ( m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v4_pre_topc(B_333,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4417,c_5254])).

tff(c_5348,plain,(
    ! [B_338] :
      ( m1_subset_1(B_338,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_338,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_338,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4426,c_4417,c_4416,c_4426,c_4417,c_5280])).

tff(c_5361,plain,(
    ! [B_339] :
      ( r1_tarski(B_339,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_339,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_339,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5348,c_12])).

tff(c_5378,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_5361])).

tff(c_5387,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5196,c_5378])).

tff(c_5389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5115,c_5387])).

tff(c_5390,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5114])).

tff(c_5409,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5390,c_4417])).

tff(c_4676,plain,(
    ! [B_303,A_304] :
      ( v3_pre_topc(u1_struct_0(B_303),A_304)
      | ~ v1_tsep_1(B_303,A_304)
      | ~ m1_subset_1(u1_struct_0(B_303),k1_zfmisc_1(u1_struct_0(A_304)))
      | ~ m1_pre_topc(B_303,A_304)
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5909,plain,(
    ! [B_358,A_359] :
      ( v3_pre_topc(u1_struct_0(B_358),A_359)
      | ~ v1_tsep_1(B_358,A_359)
      | ~ v2_pre_topc(A_359)
      | ~ m1_pre_topc(B_358,A_359)
      | ~ l1_pre_topc(A_359) ) ),
    inference(resolution,[status(thm)],[c_44,c_4676])).

tff(c_5912,plain,(
    ! [A_359] :
      ( v3_pre_topc(k2_struct_0('#skF_3'),A_359)
      | ~ v1_tsep_1('#skF_2',A_359)
      | ~ v2_pre_topc(A_359)
      | ~ m1_pre_topc('#skF_2',A_359)
      | ~ l1_pre_topc(A_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5409,c_5909])).

tff(c_4415,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_4405])).

tff(c_4456,plain,(
    ! [B_286,A_287] :
      ( m1_subset_1(u1_struct_0(B_286),k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ m1_pre_topc(B_286,A_287)
      | ~ l1_pre_topc(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4477,plain,(
    ! [B_286] :
      ( m1_subset_1(u1_struct_0(B_286),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_286,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4415,c_4456])).

tff(c_4579,plain,(
    ! [B_297] :
      ( m1_subset_1(u1_struct_0(B_297),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_297,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4477])).

tff(c_4588,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4416,c_4579])).

tff(c_4596,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4588])).

tff(c_4861,plain,(
    ! [B_312,A_313] :
      ( v1_tsep_1(B_312,A_313)
      | ~ v3_pre_topc(u1_struct_0(B_312),A_313)
      | ~ m1_subset_1(u1_struct_0(B_312),k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ m1_pre_topc(B_312,A_313)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4885,plain,(
    ! [B_312] :
      ( v1_tsep_1(B_312,'#skF_1')
      | ~ v3_pre_topc(u1_struct_0(B_312),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_312),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_312,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4415,c_4861])).

tff(c_6147,plain,(
    ! [B_380] :
      ( v1_tsep_1(B_380,'#skF_1')
      | ~ v3_pre_topc(u1_struct_0(B_380),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_380),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_380,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4885])).

tff(c_6159,plain,
    ( v1_tsep_1('#skF_3','#skF_1')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4416,c_6147])).

tff(c_6168,plain,
    ( v1_tsep_1('#skF_3','#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4596,c_4416,c_6159])).

tff(c_6169,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_4398,c_6168])).

tff(c_6174,plain,
    ( ~ v1_tsep_1('#skF_2','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_5912,c_6169])).

tff(c_6181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4397,c_58,c_4399,c_6174])).

tff(c_6183,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6182,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6187,plain,(
    ! [A_381] :
      ( u1_struct_0(A_381) = k2_struct_0(A_381)
      | ~ l1_struct_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6192,plain,(
    ! [A_382] :
      ( u1_struct_0(A_382) = k2_struct_0(A_382)
      | ~ l1_pre_topc(A_382) ) ),
    inference(resolution,[status(thm)],[c_18,c_6187])).

tff(c_6204,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_6192])).

tff(c_6214,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6204,c_46])).

tff(c_6339,plain,(
    ! [B_398,A_399] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_398),u1_pre_topc(B_398)),A_399)
      | ~ m1_pre_topc(B_398,A_399)
      | ~ l1_pre_topc(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6344,plain,(
    ! [A_399] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_399)
      | ~ m1_pre_topc('#skF_2',A_399)
      | ~ l1_pre_topc(A_399) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6204,c_6339])).

tff(c_6353,plain,(
    ! [A_400] :
      ( m1_pre_topc('#skF_3',A_400)
      | ~ m1_pre_topc('#skF_2',A_400)
      | ~ l1_pre_topc(A_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6214,c_6344])).

tff(c_6356,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6182,c_6353])).

tff(c_6359,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6356])).

tff(c_6361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6183,c_6359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:14:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.24  
% 6.38/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.24  %$ v4_pre_topc > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.38/2.24  
% 6.38/2.24  %Foreground sorts:
% 6.38/2.24  
% 6.38/2.24  
% 6.38/2.24  %Background operators:
% 6.38/2.24  
% 6.38/2.24  
% 6.38/2.24  %Foreground operators:
% 6.38/2.24  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.38/2.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.38/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.24  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.38/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.38/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.38/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.38/2.24  tff('#skF_1', type, '#skF_1': $i).
% 6.38/2.24  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.38/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.38/2.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.38/2.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.38/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.24  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.38/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.38/2.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.38/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.38/2.24  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.38/2.24  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.38/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.38/2.24  
% 6.38/2.27  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tmap_1)).
% 6.38/2.27  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 6.38/2.27  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.38/2.27  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.38/2.27  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.38/2.27  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.38/2.27  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v4_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v4_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_pre_topc)).
% 6.38/2.27  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.38/2.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.38/2.27  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 6.38/2.27  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.38/2.27  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 6.38/2.27  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 6.38/2.27  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.27  tff(c_68, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.27  tff(c_95, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_68])).
% 6.38/2.27  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.27  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.27  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.27  tff(c_20, plain, (![A_9]: (v4_pre_topc(k2_struct_0(A_9), A_9) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.38/2.27  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.38/2.27  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.27  tff(c_77, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 6.38/2.27  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.38/2.27  tff(c_98, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.38/2.27  tff(c_104, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_18, c_98])).
% 6.38/2.27  tff(c_116, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_104])).
% 6.38/2.27  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.27  tff(c_2900, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_46])).
% 6.38/2.27  tff(c_3156, plain, (![B_220, A_221]: (v4_pre_topc(B_220, g1_pre_topc(u1_struct_0(A_221), u1_pre_topc(A_221))) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_221))) | ~v4_pre_topc(B_220, A_221) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.27  tff(c_3165, plain, (![B_220]: (v4_pre_topc(B_220, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_220, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_3156])).
% 6.38/2.27  tff(c_3251, plain, (![B_226]: (v4_pre_topc(B_226, '#skF_3') | ~m1_subset_1(B_226, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_226, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116, c_2900, c_3165])).
% 6.38/2.27  tff(c_3265, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_3251])).
% 6.38/2.27  tff(c_3266, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3265])).
% 6.38/2.27  tff(c_3269, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_3266])).
% 6.38/2.28  tff(c_3273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3269])).
% 6.38/2.28  tff(c_3275, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_3265])).
% 6.38/2.28  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.28  tff(c_115, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_104])).
% 6.38/2.28  tff(c_3529, plain, (![B_242, A_243]: (m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_243), u1_pre_topc(A_243))))) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_243))) | ~v4_pre_topc(B_242, A_243) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_3549, plain, (![B_242]: (m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_242, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_3529])).
% 6.38/2.28  tff(c_3559, plain, (![B_244]: (m1_subset_1(B_244, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_244, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_244, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116, c_115, c_2900, c_3549])).
% 6.38/2.28  tff(c_3570, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_3559])).
% 6.38/2.28  tff(c_3575, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3275, c_3570])).
% 6.38/2.28  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.38/2.28  tff(c_3579, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3575, c_12])).
% 6.38/2.28  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.38/2.28  tff(c_3582, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3579, c_2])).
% 6.38/2.28  tff(c_3603, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_3582])).
% 6.38/2.28  tff(c_3639, plain, (![B_249, A_250]: (v4_pre_topc(B_249, A_250) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_250), u1_pre_topc(A_250))))) | ~v4_pre_topc(B_249, g1_pre_topc(u1_struct_0(A_250), u1_pre_topc(A_250))) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_3671, plain, (![B_249]: (v4_pre_topc(B_249, '#skF_2') | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_249, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_3639])).
% 6.38/2.28  tff(c_3689, plain, (![B_251]: (v4_pre_topc(B_251, '#skF_2') | ~m1_subset_1(B_251, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_251, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2900, c_116, c_115, c_2900, c_3671])).
% 6.38/2.28  tff(c_3713, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_3689])).
% 6.38/2.28  tff(c_3714, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3713])).
% 6.38/2.28  tff(c_3717, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3714])).
% 6.38/2.28  tff(c_3721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3717])).
% 6.38/2.28  tff(c_3723, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_3713])).
% 6.38/2.28  tff(c_3789, plain, (![B_255, A_256]: (m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_256))) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_256), u1_pre_topc(A_256))))) | ~v4_pre_topc(B_255, g1_pre_topc(u1_struct_0(A_256), u1_pre_topc(A_256))) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_3821, plain, (![B_255]: (m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_255, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_3789])).
% 6.38/2.28  tff(c_3839, plain, (![B_257]: (m1_subset_1(B_257, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_257, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_257, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2900, c_116, c_115, c_2900, c_116, c_3821])).
% 6.38/2.28  tff(c_3852, plain, (![B_258]: (r1_tarski(B_258, k2_struct_0('#skF_2')) | ~m1_subset_1(B_258, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_258, '#skF_3'))), inference(resolution, [status(thm)], [c_3839, c_12])).
% 6.38/2.28  tff(c_3869, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_3852])).
% 6.38/2.28  tff(c_3878, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3723, c_3869])).
% 6.38/2.28  tff(c_3880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3603, c_3878])).
% 6.38/2.28  tff(c_3881, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_3582])).
% 6.38/2.28  tff(c_3896, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_2900])).
% 6.38/2.28  tff(c_3897, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_116])).
% 6.38/2.28  tff(c_4337, plain, (![C_274, A_275]: (m1_pre_topc(C_274, A_275) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_274), u1_pre_topc(C_274)), A_275) | ~l1_pre_topc(C_274) | ~v2_pre_topc(C_274) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_274), u1_pre_topc(C_274))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_274), u1_pre_topc(C_274))) | ~l1_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.38/2.28  tff(c_4340, plain, (![A_275]: (m1_pre_topc('#skF_2', A_275) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_275) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_275))), inference(superposition, [status(thm), theory('equality')], [c_3897, c_4337])).
% 6.38/2.28  tff(c_4357, plain, (![A_276]: (m1_pre_topc('#skF_2', A_276) | ~m1_pre_topc('#skF_3', A_276) | ~l1_pre_topc(A_276))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3896, c_3897, c_48, c_3896, c_3897, c_54, c_52, c_3896, c_4340])).
% 6.38/2.28  tff(c_74, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.28  tff(c_97, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_74])).
% 6.38/2.28  tff(c_60, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.28  tff(c_118, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_95, c_60])).
% 6.38/2.28  tff(c_119, plain, (~v1_tsep_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_118])).
% 6.38/2.28  tff(c_124, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_46])).
% 6.38/2.28  tff(c_989, plain, (![C_101, A_102]: (m1_pre_topc(C_101, A_102) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_101), u1_pre_topc(C_101)), A_102) | ~l1_pre_topc(C_101) | ~v2_pre_topc(C_101) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_101), u1_pre_topc(C_101))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_101), u1_pre_topc(C_101))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.38/2.28  tff(c_998, plain, (![A_102]: (m1_pre_topc('#skF_2', A_102) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_102) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_102))), inference(superposition, [status(thm), theory('equality')], [c_116, c_989])).
% 6.38/2.28  tff(c_1009, plain, (![A_103]: (m1_pre_topc('#skF_2', A_103) | ~m1_pre_topc('#skF_3', A_103) | ~l1_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_124, c_116, c_48, c_124, c_116, c_54, c_52, c_124, c_998])).
% 6.38/2.28  tff(c_114, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_104])).
% 6.38/2.28  tff(c_162, plain, (![B_52, A_53]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.38/2.28  tff(c_183, plain, (![B_52]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_52, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_162])).
% 6.38/2.28  tff(c_285, plain, (![B_63]: (m1_subset_1(u1_struct_0(B_63), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_63, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_183])).
% 6.38/2.28  tff(c_309, plain, (![B_64]: (r1_tarski(u1_struct_0(B_64), k2_struct_0('#skF_1')) | ~m1_pre_topc(B_64, '#skF_1'))), inference(resolution, [status(thm)], [c_285, c_12])).
% 6.38/2.28  tff(c_317, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_116, c_309])).
% 6.38/2.28  tff(c_325, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_317])).
% 6.38/2.28  tff(c_1021, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1009, c_325])).
% 6.38/2.28  tff(c_1042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_95, c_1021])).
% 6.38/2.28  tff(c_1044, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_317])).
% 6.38/2.28  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.28  tff(c_291, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_115, c_285])).
% 6.38/2.28  tff(c_300, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_291])).
% 6.38/2.28  tff(c_1221, plain, (![B_112, A_113]: (v3_pre_topc(u1_struct_0(B_112), A_113) | ~v1_tsep_1(B_112, A_113) | ~m1_subset_1(u1_struct_0(B_112), k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.38/2.28  tff(c_1245, plain, (![B_112]: (v3_pre_topc(u1_struct_0(B_112), '#skF_1') | ~v1_tsep_1(B_112, '#skF_1') | ~m1_subset_1(u1_struct_0(B_112), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_112, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_1221])).
% 6.38/2.28  tff(c_2863, plain, (![B_195]: (v3_pre_topc(u1_struct_0(B_195), '#skF_1') | ~v1_tsep_1(B_195, '#skF_1') | ~m1_subset_1(u1_struct_0(B_195), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_195, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1245])).
% 6.38/2.28  tff(c_2875, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_115, c_2863])).
% 6.38/2.28  tff(c_2884, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_300, c_97, c_115, c_2875])).
% 6.38/2.28  tff(c_268, plain, (![B_61, A_62]: (v4_pre_topc(B_61, g1_pre_topc(u1_struct_0(A_62), u1_pre_topc(A_62))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~v4_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_274, plain, (![B_61]: (v4_pre_topc(B_61, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_61, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_268])).
% 6.38/2.28  tff(c_1196, plain, (![B_111]: (v4_pre_topc(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_111, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116, c_124, c_274])).
% 6.38/2.28  tff(c_1210, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_1196])).
% 6.38/2.28  tff(c_1211, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1210])).
% 6.38/2.28  tff(c_1214, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1211])).
% 6.38/2.28  tff(c_1218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1214])).
% 6.38/2.28  tff(c_1220, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_1210])).
% 6.38/2.28  tff(c_1352, plain, (![B_120, A_121]: (m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_121), u1_pre_topc(A_121))))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~v4_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_1369, plain, (![B_120]: (m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_120, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1352])).
% 6.38/2.28  tff(c_1511, plain, (![B_129]: (m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_129, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116, c_115, c_124, c_1369])).
% 6.38/2.28  tff(c_1522, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_1511])).
% 6.38/2.28  tff(c_1527, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1522])).
% 6.38/2.28  tff(c_1531, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1527, c_12])).
% 6.38/2.28  tff(c_1584, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1531, c_2])).
% 6.38/2.28  tff(c_1585, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1584])).
% 6.38/2.28  tff(c_1532, plain, (![B_130, A_131]: (v4_pre_topc(B_130, A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_131), u1_pre_topc(A_131))))) | ~v4_pre_topc(B_130, g1_pre_topc(u1_struct_0(A_131), u1_pre_topc(A_131))) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_1561, plain, (![B_130]: (v4_pre_topc(B_130, '#skF_2') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_130, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1532])).
% 6.38/2.28  tff(c_1586, plain, (![B_132]: (v4_pre_topc(B_132, '#skF_2') | ~m1_subset_1(B_132, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_132, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_124, c_116, c_115, c_124, c_1561])).
% 6.38/2.28  tff(c_1606, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_1586])).
% 6.38/2.28  tff(c_1607, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1606])).
% 6.38/2.28  tff(c_1610, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1607])).
% 6.38/2.28  tff(c_1614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1610])).
% 6.38/2.28  tff(c_1616, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1606])).
% 6.38/2.28  tff(c_1635, plain, (![B_134, A_135]: (m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135))))) | ~v4_pre_topc(B_134, g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_1664, plain, (![B_134]: (m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_134, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1635])).
% 6.38/2.28  tff(c_1713, plain, (![B_138]: (m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_138, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_124, c_116, c_115, c_124, c_116, c_1664])).
% 6.38/2.28  tff(c_1738, plain, (![B_140]: (r1_tarski(B_140, k2_struct_0('#skF_2')) | ~m1_subset_1(B_140, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_140, '#skF_3'))), inference(resolution, [status(thm)], [c_1713, c_12])).
% 6.38/2.28  tff(c_1755, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_1738])).
% 6.38/2.28  tff(c_1764, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_1755])).
% 6.38/2.28  tff(c_1766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1585, c_1764])).
% 6.38/2.28  tff(c_1767, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1584])).
% 6.38/2.28  tff(c_1786, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_116])).
% 6.38/2.28  tff(c_44, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.38/2.28  tff(c_1067, plain, (![B_104, A_105]: (v1_tsep_1(B_104, A_105) | ~v3_pre_topc(u1_struct_0(B_104), A_105) | ~m1_subset_1(u1_struct_0(B_104), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.38/2.28  tff(c_2345, plain, (![B_165, A_166]: (v1_tsep_1(B_165, A_166) | ~v3_pre_topc(u1_struct_0(B_165), A_166) | ~v2_pre_topc(A_166) | ~m1_pre_topc(B_165, A_166) | ~l1_pre_topc(A_166))), inference(resolution, [status(thm)], [c_44, c_1067])).
% 6.38/2.28  tff(c_2351, plain, (![A_166]: (v1_tsep_1('#skF_2', A_166) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_166) | ~v2_pre_topc(A_166) | ~m1_pre_topc('#skF_2', A_166) | ~l1_pre_topc(A_166))), inference(superposition, [status(thm), theory('equality')], [c_1786, c_2345])).
% 6.38/2.28  tff(c_2889, plain, (v1_tsep_1('#skF_2', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2884, c_2351])).
% 6.38/2.28  tff(c_2895, plain, (v1_tsep_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1044, c_58, c_2889])).
% 6.38/2.28  tff(c_2897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_2895])).
% 6.38/2.28  tff(c_2898, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_118])).
% 6.38/2.28  tff(c_4377, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4357, c_2898])).
% 6.38/2.28  tff(c_4396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_95, c_4377])).
% 6.38/2.28  tff(c_4397, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_74])).
% 6.38/2.28  tff(c_4398, plain, (~v1_tsep_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_74])).
% 6.38/2.28  tff(c_76, plain, (v1_tsep_1('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.38/2.28  tff(c_4399, plain, (v1_tsep_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_4398, c_76])).
% 6.38/2.28  tff(c_4400, plain, (![A_277]: (u1_struct_0(A_277)=k2_struct_0(A_277) | ~l1_struct_0(A_277))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.38/2.28  tff(c_4405, plain, (![A_278]: (u1_struct_0(A_278)=k2_struct_0(A_278) | ~l1_pre_topc(A_278))), inference(resolution, [status(thm)], [c_18, c_4400])).
% 6.38/2.28  tff(c_4417, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_4405])).
% 6.38/2.28  tff(c_4426, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4417, c_46])).
% 6.38/2.28  tff(c_4612, plain, (![B_298, A_299]: (v4_pre_topc(B_298, g1_pre_topc(u1_struct_0(A_299), u1_pre_topc(A_299))) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_299))) | ~v4_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_4615, plain, (![B_298]: (v4_pre_topc(B_298, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_298, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4417, c_4612])).
% 6.38/2.28  tff(c_4836, plain, (![B_311]: (v4_pre_topc(B_311, '#skF_3') | ~m1_subset_1(B_311, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_311, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4417, c_4426, c_4615])).
% 6.38/2.28  tff(c_4850, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_4836])).
% 6.38/2.28  tff(c_4851, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_4850])).
% 6.38/2.28  tff(c_4854, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_4851])).
% 6.38/2.28  tff(c_4858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4854])).
% 6.38/2.28  tff(c_4860, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_4850])).
% 6.38/2.28  tff(c_4416, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_4405])).
% 6.38/2.28  tff(c_4975, plain, (![B_320, A_321]: (m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_321), u1_pre_topc(A_321))))) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_321))) | ~v4_pre_topc(B_320, A_321) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_4989, plain, (![B_320]: (m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(B_320, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4417, c_4975])).
% 6.38/2.28  tff(c_5091, plain, (![B_326]: (m1_subset_1(B_326, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_326, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v4_pre_topc(B_326, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4417, c_4416, c_4426, c_4989])).
% 6.38/2.28  tff(c_5102, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_77, c_5091])).
% 6.38/2.28  tff(c_5107, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4860, c_5102])).
% 6.38/2.28  tff(c_5111, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_5107, c_12])).
% 6.38/2.28  tff(c_5114, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_5111, c_2])).
% 6.38/2.28  tff(c_5115, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_5114])).
% 6.38/2.28  tff(c_5116, plain, (![B_327, A_328]: (v4_pre_topc(B_327, A_328) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_328), u1_pre_topc(A_328))))) | ~v4_pre_topc(B_327, g1_pre_topc(u1_struct_0(A_328), u1_pre_topc(A_328))) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_5142, plain, (![B_327]: (v4_pre_topc(B_327, '#skF_2') | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_327, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4417, c_5116])).
% 6.38/2.28  tff(c_5166, plain, (![B_329]: (v4_pre_topc(B_329, '#skF_2') | ~m1_subset_1(B_329, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_329, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4426, c_4417, c_4416, c_4426, c_5142])).
% 6.38/2.28  tff(c_5186, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_5166])).
% 6.38/2.28  tff(c_5187, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5186])).
% 6.38/2.28  tff(c_5190, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_5187])).
% 6.38/2.28  tff(c_5194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_5190])).
% 6.38/2.28  tff(c_5196, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_5186])).
% 6.38/2.28  tff(c_5254, plain, (![B_333, A_334]: (m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0(A_334))) | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_334), u1_pre_topc(A_334))))) | ~v4_pre_topc(B_333, g1_pre_topc(u1_struct_0(A_334), u1_pre_topc(A_334))) | ~l1_pre_topc(A_334) | ~v2_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.38/2.28  tff(c_5280, plain, (![B_333]: (m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v4_pre_topc(B_333, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4417, c_5254])).
% 6.38/2.28  tff(c_5348, plain, (![B_338]: (m1_subset_1(B_338, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_338, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_338, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4426, c_4417, c_4416, c_4426, c_4417, c_5280])).
% 6.38/2.28  tff(c_5361, plain, (![B_339]: (r1_tarski(B_339, k2_struct_0('#skF_2')) | ~m1_subset_1(B_339, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v4_pre_topc(B_339, '#skF_3'))), inference(resolution, [status(thm)], [c_5348, c_12])).
% 6.38/2.28  tff(c_5378, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_77, c_5361])).
% 6.38/2.28  tff(c_5387, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5196, c_5378])).
% 6.38/2.28  tff(c_5389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5115, c_5387])).
% 6.38/2.28  tff(c_5390, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5114])).
% 6.38/2.28  tff(c_5409, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5390, c_4417])).
% 6.38/2.28  tff(c_4676, plain, (![B_303, A_304]: (v3_pre_topc(u1_struct_0(B_303), A_304) | ~v1_tsep_1(B_303, A_304) | ~m1_subset_1(u1_struct_0(B_303), k1_zfmisc_1(u1_struct_0(A_304))) | ~m1_pre_topc(B_303, A_304) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.38/2.28  tff(c_5909, plain, (![B_358, A_359]: (v3_pre_topc(u1_struct_0(B_358), A_359) | ~v1_tsep_1(B_358, A_359) | ~v2_pre_topc(A_359) | ~m1_pre_topc(B_358, A_359) | ~l1_pre_topc(A_359))), inference(resolution, [status(thm)], [c_44, c_4676])).
% 6.38/2.28  tff(c_5912, plain, (![A_359]: (v3_pre_topc(k2_struct_0('#skF_3'), A_359) | ~v1_tsep_1('#skF_2', A_359) | ~v2_pre_topc(A_359) | ~m1_pre_topc('#skF_2', A_359) | ~l1_pre_topc(A_359))), inference(superposition, [status(thm), theory('equality')], [c_5409, c_5909])).
% 6.38/2.28  tff(c_4415, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_4405])).
% 6.38/2.28  tff(c_4456, plain, (![B_286, A_287]: (m1_subset_1(u1_struct_0(B_286), k1_zfmisc_1(u1_struct_0(A_287))) | ~m1_pre_topc(B_286, A_287) | ~l1_pre_topc(A_287))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.38/2.28  tff(c_4477, plain, (![B_286]: (m1_subset_1(u1_struct_0(B_286), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_286, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4415, c_4456])).
% 6.38/2.28  tff(c_4579, plain, (![B_297]: (m1_subset_1(u1_struct_0(B_297), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_297, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4477])).
% 6.38/2.28  tff(c_4588, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4416, c_4579])).
% 6.38/2.28  tff(c_4596, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4588])).
% 6.38/2.28  tff(c_4861, plain, (![B_312, A_313]: (v1_tsep_1(B_312, A_313) | ~v3_pre_topc(u1_struct_0(B_312), A_313) | ~m1_subset_1(u1_struct_0(B_312), k1_zfmisc_1(u1_struct_0(A_313))) | ~m1_pre_topc(B_312, A_313) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.38/2.28  tff(c_4885, plain, (![B_312]: (v1_tsep_1(B_312, '#skF_1') | ~v3_pre_topc(u1_struct_0(B_312), '#skF_1') | ~m1_subset_1(u1_struct_0(B_312), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_312, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4415, c_4861])).
% 6.38/2.28  tff(c_6147, plain, (![B_380]: (v1_tsep_1(B_380, '#skF_1') | ~v3_pre_topc(u1_struct_0(B_380), '#skF_1') | ~m1_subset_1(u1_struct_0(B_380), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_380, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4885])).
% 6.38/2.28  tff(c_6159, plain, (v1_tsep_1('#skF_3', '#skF_1') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4416, c_6147])).
% 6.38/2.28  tff(c_6168, plain, (v1_tsep_1('#skF_3', '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4596, c_4416, c_6159])).
% 6.38/2.28  tff(c_6169, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_4398, c_6168])).
% 6.38/2.28  tff(c_6174, plain, (~v1_tsep_1('#skF_2', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_5912, c_6169])).
% 6.38/2.28  tff(c_6181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_4397, c_58, c_4399, c_6174])).
% 6.38/2.28  tff(c_6183, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 6.38/2.28  tff(c_6182, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 6.38/2.28  tff(c_6187, plain, (![A_381]: (u1_struct_0(A_381)=k2_struct_0(A_381) | ~l1_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.38/2.28  tff(c_6192, plain, (![A_382]: (u1_struct_0(A_382)=k2_struct_0(A_382) | ~l1_pre_topc(A_382))), inference(resolution, [status(thm)], [c_18, c_6187])).
% 6.38/2.28  tff(c_6204, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_6192])).
% 6.38/2.28  tff(c_6214, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6204, c_46])).
% 6.38/2.28  tff(c_6339, plain, (![B_398, A_399]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_398), u1_pre_topc(B_398)), A_399) | ~m1_pre_topc(B_398, A_399) | ~l1_pre_topc(A_399))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.38/2.28  tff(c_6344, plain, (![A_399]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_399) | ~m1_pre_topc('#skF_2', A_399) | ~l1_pre_topc(A_399))), inference(superposition, [status(thm), theory('equality')], [c_6204, c_6339])).
% 6.38/2.28  tff(c_6353, plain, (![A_400]: (m1_pre_topc('#skF_3', A_400) | ~m1_pre_topc('#skF_2', A_400) | ~l1_pre_topc(A_400))), inference(demodulation, [status(thm), theory('equality')], [c_6214, c_6344])).
% 6.38/2.28  tff(c_6356, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6182, c_6353])).
% 6.38/2.28  tff(c_6359, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6356])).
% 6.38/2.28  tff(c_6361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6183, c_6359])).
% 6.38/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.28  
% 6.38/2.28  Inference rules
% 6.38/2.28  ----------------------
% 6.38/2.28  #Ref     : 0
% 6.38/2.28  #Sup     : 1299
% 6.38/2.28  #Fact    : 0
% 6.38/2.28  #Define  : 0
% 6.38/2.28  #Split   : 48
% 6.38/2.28  #Chain   : 0
% 6.38/2.28  #Close   : 0
% 6.38/2.28  
% 6.38/2.28  Ordering : KBO
% 6.38/2.28  
% 6.38/2.28  Simplification rules
% 6.38/2.28  ----------------------
% 6.38/2.28  #Subsume      : 422
% 6.38/2.28  #Demod        : 1504
% 6.38/2.28  #Tautology    : 310
% 6.38/2.28  #SimpNegUnit  : 22
% 6.38/2.28  #BackRed      : 52
% 6.38/2.28  
% 6.38/2.28  #Partial instantiations: 0
% 6.38/2.28  #Strategies tried      : 1
% 6.38/2.28  
% 6.38/2.28  Timing (in seconds)
% 6.38/2.28  ----------------------
% 6.38/2.28  Preprocessing        : 0.34
% 6.38/2.28  Parsing              : 0.18
% 6.38/2.28  CNF conversion       : 0.02
% 6.38/2.28  Main loop            : 1.16
% 6.38/2.28  Inferencing          : 0.38
% 6.38/2.28  Reduction            : 0.42
% 6.38/2.28  Demodulation         : 0.29
% 6.38/2.28  BG Simplification    : 0.04
% 6.38/2.28  Subsumption          : 0.22
% 6.76/2.28  Abstraction          : 0.06
% 6.76/2.28  MUC search           : 0.00
% 6.76/2.28  Cooper               : 0.00
% 6.76/2.28  Total                : 1.57
% 6.76/2.28  Index Insertion      : 0.00
% 6.76/2.28  Index Deletion       : 0.00
% 6.76/2.28  Index Matching       : 0.00
% 6.76/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
