%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:24 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :  241 (2625 expanded)
%              Number of leaves         :   32 ( 940 expanded)
%              Depth                    :   17
%              Number of atoms          :  570 (8359 expanded)
%              Number of equality atoms :   36 (1379 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_134,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

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

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

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

tff(f_84,axiom,(
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

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_102,axiom,(
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

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_66,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_92,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    ! [A_12] :
      ( v3_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_18,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_18,c_94])).

tff(c_112,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_42,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2699,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_42])).

tff(c_2785,plain,(
    ! [B_188,A_189] :
      ( v3_pre_topc(B_188,g1_pre_topc(u1_struct_0(A_189),u1_pre_topc(A_189)))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ v3_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2788,plain,(
    ! [B_188] :
      ( v3_pre_topc(B_188,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_188,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2785])).

tff(c_3102,plain,(
    ! [B_206] :
      ( v3_pre_topc(B_206,'#skF_3')
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_206,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_112,c_2699,c_2788])).

tff(c_3116,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_3102])).

tff(c_3147,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3116])).

tff(c_3150,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_3147])).

tff(c_3154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3150])).

tff(c_3156,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3116])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_111,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_100])).

tff(c_3117,plain,(
    ! [B_207,A_208] :
      ( m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_208),u1_pre_topc(A_208)))))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ v3_pre_topc(B_207,A_208)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3131,plain,(
    ! [B_207] :
      ( m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_207,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_3117])).

tff(c_3157,plain,(
    ! [B_209] :
      ( m1_subset_1(B_209,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_209,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_112,c_111,c_2699,c_3131])).

tff(c_3171,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_3157])).

tff(c_3185,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3156,c_3171])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3189,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3185,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3192,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3189,c_2])).

tff(c_3193,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3192])).

tff(c_3194,plain,(
    ! [B_211,A_212] :
      ( v3_pre_topc(B_211,A_212)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_212),u1_pre_topc(A_212)))))
      | ~ v3_pre_topc(B_211,g1_pre_topc(u1_struct_0(A_212),u1_pre_topc(A_212)))
      | ~ l1_pre_topc(A_212)
      | ~ v2_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3216,plain,(
    ! [B_211] :
      ( v3_pre_topc(B_211,'#skF_2')
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_211,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_3194])).

tff(c_3244,plain,(
    ! [B_213] :
      ( v3_pre_topc(B_213,'#skF_2')
      | ~ m1_subset_1(B_213,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_213,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2699,c_112,c_111,c_2699,c_3216])).

tff(c_3264,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_3244])).

tff(c_3265,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3264])).

tff(c_3288,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_3265])).

tff(c_3292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3288])).

tff(c_3294,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3264])).

tff(c_3328,plain,(
    ! [B_217,A_218] :
      ( m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_218),u1_pre_topc(A_218)))))
      | ~ v3_pre_topc(B_217,g1_pre_topc(u1_struct_0(A_218),u1_pre_topc(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3350,plain,(
    ! [B_217] :
      ( m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_217,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_3328])).

tff(c_3397,plain,(
    ! [B_220] :
      ( m1_subset_1(B_220,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_220,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2699,c_112,c_111,c_2699,c_112,c_3350])).

tff(c_3431,plain,(
    ! [B_223] :
      ( r1_tarski(B_223,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_223,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3397,c_12])).

tff(c_3448,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_3431])).

tff(c_3457,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3294,c_3448])).

tff(c_3459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3193,c_3457])).

tff(c_3460,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3192])).

tff(c_3473,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3460,c_2699])).

tff(c_3474,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3460,c_112])).

tff(c_3938,plain,(
    ! [C_244,A_245] :
      ( m1_pre_topc(C_244,A_245)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_244),u1_pre_topc(C_244)),A_245)
      | ~ l1_pre_topc(C_244)
      | ~ v2_pre_topc(C_244)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_244),u1_pre_topc(C_244)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_244),u1_pre_topc(C_244)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3944,plain,(
    ! [A_245] :
      ( m1_pre_topc('#skF_2',A_245)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_245)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3474,c_3938])).

tff(c_3958,plain,(
    ! [A_246] :
      ( m1_pre_topc('#skF_2',A_246)
      | ~ m1_pre_topc('#skF_3',A_246)
      | ~ l1_pre_topc(A_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3473,c_3474,c_44,c_3473,c_3474,c_50,c_48,c_3473,c_3944])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_72,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_91,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_40,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_924,plain,(
    ! [B_92,A_93] :
      ( v3_pre_topc(u1_struct_0(B_92),A_93)
      | ~ v1_tsep_1(B_92,A_93)
      | ~ m1_subset_1(u1_struct_0(B_92),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2168,plain,(
    ! [B_150,A_151] :
      ( v3_pre_topc(u1_struct_0(B_150),A_151)
      | ~ v1_tsep_1(B_150,A_151)
      | ~ v2_pre_topc(A_151)
      | ~ m1_pre_topc(B_150,A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_40,c_924])).

tff(c_2189,plain,(
    ! [A_151] :
      ( v3_pre_topc(k2_struct_0('#skF_3'),A_151)
      | ~ v1_tsep_1('#skF_3',A_151)
      | ~ v2_pre_topc(A_151)
      | ~ m1_pre_topc('#skF_3',A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_2168])).

tff(c_56,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_114,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_92,c_56])).

tff(c_115,plain,(
    ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_124,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_42])).

tff(c_866,plain,(
    ! [C_89,A_90] :
      ( m1_pre_topc(C_89,A_90)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_89),u1_pre_topc(C_89)),A_90)
      | ~ l1_pre_topc(C_89)
      | ~ v2_pre_topc(C_89)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_89),u1_pre_topc(C_89)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_89),u1_pre_topc(C_89)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_869,plain,(
    ! [A_90] :
      ( m1_pre_topc('#skF_2',A_90)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_90)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_866])).

tff(c_882,plain,(
    ! [A_91] :
      ( m1_pre_topc('#skF_2',A_91)
      | ~ m1_pre_topc('#skF_3',A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_124,c_112,c_44,c_124,c_112,c_50,c_48,c_124,c_869])).

tff(c_110,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_100])).

tff(c_152,plain,(
    ! [B_47,A_48] :
      ( m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_173,plain,(
    ! [B_47] :
      ( m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_47,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_152])).

tff(c_259,plain,(
    ! [B_55] :
      ( m1_subset_1(u1_struct_0(B_55),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_55,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_173])).

tff(c_324,plain,(
    ! [B_58] :
      ( r1_tarski(u1_struct_0(B_58),k2_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_58,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_259,c_12])).

tff(c_329,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_324])).

tff(c_340,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_894,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_882,c_340])).

tff(c_910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_92,c_894])).

tff(c_912,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_268,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_259])).

tff(c_274,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_268])).

tff(c_212,plain,(
    ! [B_51,A_52] :
      ( v3_pre_topc(B_51,g1_pre_topc(u1_struct_0(A_52),u1_pre_topc(A_52)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ v3_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_215,plain,(
    ! [B_51] :
      ( v3_pre_topc(B_51,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_51,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_212])).

tff(c_1103,plain,(
    ! [B_102] :
      ( v3_pre_topc(B_102,'#skF_3')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_102,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_112,c_124,c_215])).

tff(c_1117,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_1103])).

tff(c_1118,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1117])).

tff(c_1121,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1118])).

tff(c_1125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1121])).

tff(c_1127,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1117])).

tff(c_1073,plain,(
    ! [B_100,A_101] :
      ( m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_101),u1_pre_topc(A_101)))))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v3_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1087,plain,(
    ! [B_100] :
      ( m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_100,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1073])).

tff(c_1269,plain,(
    ! [B_110] :
      ( m1_subset_1(B_110,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_110,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_112,c_111,c_124,c_1087])).

tff(c_1280,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_1269])).

tff(c_1285,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_1280])).

tff(c_1295,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1285,c_12])).

tff(c_1298,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1295,c_2])).

tff(c_1299,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1298])).

tff(c_1194,plain,(
    ! [B_107,A_108] :
      ( v3_pre_topc(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_108),u1_pre_topc(A_108)))))
      | ~ v3_pre_topc(B_107,g1_pre_topc(u1_struct_0(A_108),u1_pre_topc(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1220,plain,(
    ! [B_107] :
      ( v3_pre_topc(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_107,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1194])).

tff(c_1244,plain,(
    ! [B_109] :
      ( v3_pre_topc(B_109,'#skF_2')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_109,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_124,c_112,c_111,c_124,c_1220])).

tff(c_1258,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_1244])).

tff(c_1259,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1258])).

tff(c_1262,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1259])).

tff(c_1266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1262])).

tff(c_1268,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1258])).

tff(c_1300,plain,(
    ! [B_111,A_112] :
      ( m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_112),u1_pre_topc(A_112)))))
      | ~ v3_pre_topc(B_111,g1_pre_topc(u1_struct_0(A_112),u1_pre_topc(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1326,plain,(
    ! [B_111] :
      ( m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_111,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1300])).

tff(c_1387,plain,(
    ! [B_115] :
      ( m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_115,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_124,c_112,c_111,c_124,c_112,c_1326])).

tff(c_1421,plain,(
    ! [B_118] :
      ( r1_tarski(B_118,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_118,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1387,c_12])).

tff(c_1438,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_1421])).

tff(c_1447,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_1438])).

tff(c_1449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1299,c_1447])).

tff(c_1450,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1298])).

tff(c_1517,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_112])).

tff(c_280,plain,(
    ! [B_56,A_57] :
      ( v1_tsep_1(B_56,A_57)
      | ~ v3_pre_topc(u1_struct_0(B_56),A_57)
      | ~ m1_subset_1(u1_struct_0(B_56),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_304,plain,(
    ! [B_56] :
      ( v1_tsep_1(B_56,'#skF_1')
      | ~ v3_pre_topc(u1_struct_0(B_56),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_56),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_56,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_280])).

tff(c_2650,plain,(
    ! [B_176] :
      ( v1_tsep_1(B_176,'#skF_1')
      | ~ v3_pre_topc(u1_struct_0(B_176),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_176),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_176,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_304])).

tff(c_2653,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | ~ v3_pre_topc(u1_struct_0('#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_2650])).

tff(c_2667,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_274,c_1517,c_2653])).

tff(c_2668,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_2667])).

tff(c_2680,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2189,c_2668])).

tff(c_2687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_92,c_54,c_91,c_2680])).

tff(c_2688,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_3970,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3958,c_2688])).

tff(c_3981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_92,c_3970])).

tff(c_3983,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3990,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3983,c_64])).

tff(c_3985,plain,(
    ! [A_247] :
      ( u1_struct_0(A_247) = k2_struct_0(A_247)
      | ~ l1_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3991,plain,(
    ! [A_248] :
      ( u1_struct_0(A_248) = k2_struct_0(A_248)
      | ~ l1_pre_topc(A_248) ) ),
    inference(resolution,[status(thm)],[c_18,c_3985])).

tff(c_4003,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3991])).

tff(c_4013,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4003,c_42])).

tff(c_4755,plain,(
    ! [C_298,A_299] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_298),u1_pre_topc(C_298)),A_299)
      | ~ m1_pre_topc(C_298,A_299)
      | ~ l1_pre_topc(C_298)
      | ~ v2_pre_topc(C_298)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_298),u1_pre_topc(C_298)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_298),u1_pre_topc(C_298)))
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4767,plain,(
    ! [A_299] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_299)
      | ~ m1_pre_topc('#skF_2',A_299)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4003,c_4755])).

tff(c_4789,plain,(
    ! [A_300] :
      ( m1_pre_topc('#skF_3',A_300)
      | ~ m1_pre_topc('#skF_2',A_300)
      | ~ l1_pre_topc(A_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4013,c_4003,c_44,c_4013,c_4003,c_50,c_48,c_4013,c_4767])).

tff(c_4792,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3990,c_4789])).

tff(c_4795,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4792])).

tff(c_4797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3983,c_4795])).

tff(c_4799,plain,(
    ~ v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4800,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_4799,c_70])).

tff(c_4798,plain,(
    v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4801,plain,(
    ! [A_301] :
      ( u1_struct_0(A_301) = k2_struct_0(A_301)
      | ~ l1_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4808,plain,(
    ! [A_302] :
      ( u1_struct_0(A_302) = k2_struct_0(A_302)
      | ~ l1_pre_topc(A_302) ) ),
    inference(resolution,[status(thm)],[c_18,c_4801])).

tff(c_4820,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_4808])).

tff(c_4830,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4820,c_42])).

tff(c_4903,plain,(
    ! [B_313,A_314] :
      ( v3_pre_topc(B_313,g1_pre_topc(u1_struct_0(A_314),u1_pre_topc(A_314)))
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ v3_pre_topc(B_313,A_314)
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4906,plain,(
    ! [B_313] :
      ( v3_pre_topc(B_313,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_313,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4820,c_4903])).

tff(c_5772,plain,(
    ! [B_361] :
      ( v3_pre_topc(B_361,'#skF_3')
      | ~ m1_subset_1(B_361,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_361,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4820,c_4830,c_4906])).

tff(c_5786,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_5772])).

tff(c_5787,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5786])).

tff(c_5790,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_5787])).

tff(c_5794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_5790])).

tff(c_5796,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_5786])).

tff(c_4819,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_4808])).

tff(c_5655,plain,(
    ! [B_354,A_355] :
      ( m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_355),u1_pre_topc(A_355)))))
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ v3_pre_topc(B_354,A_355)
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5669,plain,(
    ! [B_354] :
      ( m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_354,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4820,c_5655])).

tff(c_6040,plain,(
    ! [B_374] :
      ( m1_subset_1(B_374,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_374,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_374,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4820,c_4819,c_4830,c_5669])).

tff(c_6051,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_6040])).

tff(c_6056,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5796,c_6051])).

tff(c_6066,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6056,c_12])).

tff(c_6075,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6066,c_2])).

tff(c_6076,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6075])).

tff(c_5797,plain,(
    ! [B_362,A_363] :
      ( v3_pre_topc(B_362,A_363)
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_363),u1_pre_topc(A_363)))))
      | ~ v3_pre_topc(B_362,g1_pre_topc(u1_struct_0(A_363),u1_pre_topc(A_363)))
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5807,plain,(
    ! [B_362] :
      ( v3_pre_topc(B_362,'#skF_2')
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_362,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4820,c_5797])).

tff(c_5919,plain,(
    ! [B_368] :
      ( v3_pre_topc(B_368,'#skF_2')
      | ~ m1_subset_1(B_368,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_368,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4830,c_4820,c_4819,c_4830,c_5807])).

tff(c_5933,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_5919])).

tff(c_5934,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5933])).

tff(c_5937,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_5934])).

tff(c_5941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_5937])).

tff(c_5943,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5933])).

tff(c_5944,plain,(
    ! [B_369,A_370] :
      ( m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_370),u1_pre_topc(A_370)))))
      | ~ v3_pre_topc(B_369,g1_pre_topc(u1_struct_0(A_370),u1_pre_topc(A_370)))
      | ~ l1_pre_topc(A_370)
      | ~ v2_pre_topc(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5966,plain,(
    ! [B_369] :
      ( m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_369,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4820,c_5944])).

tff(c_6109,plain,(
    ! [B_379] :
      ( m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_379,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4830,c_4820,c_4819,c_4830,c_4820,c_5966])).

tff(c_6134,plain,(
    ! [B_381] :
      ( r1_tarski(B_381,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_381,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_381,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6109,c_12])).

tff(c_6151,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_6134])).

tff(c_6160,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_6151])).

tff(c_6162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6076,c_6160])).

tff(c_6163,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6075])).

tff(c_6180,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6163,c_4820])).

tff(c_4975,plain,(
    ! [B_318,A_319] :
      ( v3_pre_topc(u1_struct_0(B_318),A_319)
      | ~ v1_tsep_1(B_318,A_319)
      | ~ m1_subset_1(u1_struct_0(B_318),k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ m1_pre_topc(B_318,A_319)
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6782,plain,(
    ! [B_410,A_411] :
      ( v3_pre_topc(u1_struct_0(B_410),A_411)
      | ~ v1_tsep_1(B_410,A_411)
      | ~ v2_pre_topc(A_411)
      | ~ m1_pre_topc(B_410,A_411)
      | ~ l1_pre_topc(A_411) ) ),
    inference(resolution,[status(thm)],[c_40,c_4975])).

tff(c_6800,plain,(
    ! [A_411] :
      ( v3_pre_topc(k2_struct_0('#skF_3'),A_411)
      | ~ v1_tsep_1('#skF_2',A_411)
      | ~ v2_pre_topc(A_411)
      | ~ m1_pre_topc('#skF_2',A_411)
      | ~ l1_pre_topc(A_411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6180,c_6782])).

tff(c_4818,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_4808])).

tff(c_4859,plain,(
    ! [B_310,A_311] :
      ( m1_subset_1(u1_struct_0(B_310),k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4880,plain,(
    ! [B_310] :
      ( m1_subset_1(u1_struct_0(B_310),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_310,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4818,c_4859])).

tff(c_4935,plain,(
    ! [B_316] :
      ( m1_subset_1(u1_struct_0(B_316),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_316,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4880])).

tff(c_4959,plain,(
    ! [B_317] :
      ( r1_tarski(u1_struct_0(B_317),k2_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_317,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4935,c_12])).

tff(c_4967,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4819,c_4959])).

tff(c_5016,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4967])).

tff(c_5544,plain,(
    ! [C_347,A_348] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_347),u1_pre_topc(C_347)),A_348)
      | ~ m1_pre_topc(C_347,A_348)
      | ~ l1_pre_topc(C_347)
      | ~ v2_pre_topc(C_347)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_347),u1_pre_topc(C_347)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_347),u1_pre_topc(C_347)))
      | ~ l1_pre_topc(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5547,plain,(
    ! [A_348] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_348)
      | ~ m1_pre_topc('#skF_2',A_348)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4820,c_5544])).

tff(c_5560,plain,(
    ! [A_349] :
      ( m1_pre_topc('#skF_3',A_349)
      | ~ m1_pre_topc('#skF_2',A_349)
      | ~ l1_pre_topc(A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4830,c_4820,c_44,c_4830,c_4820,c_50,c_48,c_4830,c_5547])).

tff(c_5563,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4800,c_5560])).

tff(c_5566,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5563])).

tff(c_5568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5016,c_5566])).

tff(c_5570,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4967])).

tff(c_4944,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4819,c_4935])).

tff(c_5647,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5570,c_4944])).

tff(c_5605,plain,(
    ! [B_352,A_353] :
      ( v1_tsep_1(B_352,A_353)
      | ~ v3_pre_topc(u1_struct_0(B_352),A_353)
      | ~ m1_subset_1(u1_struct_0(B_352),k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ m1_pre_topc(B_352,A_353)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5629,plain,(
    ! [B_352] :
      ( v1_tsep_1(B_352,'#skF_1')
      | ~ v3_pre_topc(u1_struct_0(B_352),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_352),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_352,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4818,c_5605])).

tff(c_7218,plain,(
    ! [B_434] :
      ( v1_tsep_1(B_434,'#skF_1')
      | ~ v3_pre_topc(u1_struct_0(B_434),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_434),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_434,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5629])).

tff(c_7227,plain,
    ( v1_tsep_1('#skF_3','#skF_1')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4819,c_7218])).

tff(c_7238,plain,
    ( v1_tsep_1('#skF_3','#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5570,c_5647,c_4819,c_7227])).

tff(c_7239,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_4799,c_7238])).

tff(c_7245,plain,
    ( ~ v1_tsep_1('#skF_2','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6800,c_7239])).

tff(c_7252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4800,c_54,c_4798,c_7245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.47  
% 7.01/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.47  %$ v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.01/2.47  
% 7.01/2.47  %Foreground sorts:
% 7.01/2.47  
% 7.01/2.47  
% 7.01/2.47  %Background operators:
% 7.01/2.47  
% 7.01/2.47  
% 7.01/2.47  %Foreground operators:
% 7.01/2.47  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.01/2.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.01/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.01/2.47  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.01/2.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.01/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.01/2.47  tff('#skF_2', type, '#skF_2': $i).
% 7.01/2.47  tff('#skF_3', type, '#skF_3': $i).
% 7.01/2.47  tff('#skF_1', type, '#skF_1': $i).
% 7.01/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.01/2.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.01/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.01/2.47  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 7.01/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.01/2.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.01/2.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.01/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.01/2.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.01/2.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.01/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.01/2.47  
% 7.01/2.51  tff(f_134, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tmap_1)).
% 7.01/2.51  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 7.01/2.51  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.01/2.51  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.01/2.51  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.01/2.51  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.01/2.51  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 7.01/2.51  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.01/2.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.01/2.51  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 7.01/2.51  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.01/2.51  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 7.01/2.51  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_66, plain, (v1_tsep_1('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_92, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 7.01/2.51  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_28, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.01/2.51  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.01/2.51  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.01/2.51  tff(c_73, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 7.01/2.51  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.01/2.51  tff(c_94, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.01/2.51  tff(c_100, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_18, c_94])).
% 7.01/2.51  tff(c_112, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_100])).
% 7.01/2.51  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_2699, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_42])).
% 7.01/2.51  tff(c_2785, plain, (![B_188, A_189]: (v3_pre_topc(B_188, g1_pre_topc(u1_struct_0(A_189), u1_pre_topc(A_189))) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~v3_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_2788, plain, (![B_188]: (v3_pre_topc(B_188, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_188, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2785])).
% 7.01/2.51  tff(c_3102, plain, (![B_206]: (v3_pre_topc(B_206, '#skF_3') | ~m1_subset_1(B_206, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_206, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112, c_2699, c_2788])).
% 7.01/2.51  tff(c_3116, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_3102])).
% 7.01/2.51  tff(c_3147, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3116])).
% 7.01/2.51  tff(c_3150, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_3147])).
% 7.01/2.51  tff(c_3154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3150])).
% 7.01/2.51  tff(c_3156, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_3116])).
% 7.01/2.51  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_111, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_100])).
% 7.01/2.51  tff(c_3117, plain, (![B_207, A_208]: (m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_208), u1_pre_topc(A_208))))) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_208))) | ~v3_pre_topc(B_207, A_208) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_3131, plain, (![B_207]: (m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_207, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_3117])).
% 7.01/2.51  tff(c_3157, plain, (![B_209]: (m1_subset_1(B_209, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_209, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_209, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112, c_111, c_2699, c_3131])).
% 7.01/2.51  tff(c_3171, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_3157])).
% 7.01/2.51  tff(c_3185, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3156, c_3171])).
% 7.01/2.51  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.01/2.51  tff(c_3189, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3185, c_12])).
% 7.01/2.51  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.01/2.51  tff(c_3192, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3189, c_2])).
% 7.01/2.51  tff(c_3193, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_3192])).
% 7.01/2.51  tff(c_3194, plain, (![B_211, A_212]: (v3_pre_topc(B_211, A_212) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_212), u1_pre_topc(A_212))))) | ~v3_pre_topc(B_211, g1_pre_topc(u1_struct_0(A_212), u1_pre_topc(A_212))) | ~l1_pre_topc(A_212) | ~v2_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_3216, plain, (![B_211]: (v3_pre_topc(B_211, '#skF_2') | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_211, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_3194])).
% 7.01/2.51  tff(c_3244, plain, (![B_213]: (v3_pre_topc(B_213, '#skF_2') | ~m1_subset_1(B_213, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_213, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2699, c_112, c_111, c_2699, c_3216])).
% 7.01/2.51  tff(c_3264, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_3244])).
% 7.01/2.51  tff(c_3265, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3264])).
% 7.01/2.51  tff(c_3288, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_3265])).
% 7.01/2.51  tff(c_3292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3288])).
% 7.01/2.51  tff(c_3294, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_3264])).
% 7.01/2.51  tff(c_3328, plain, (![B_217, A_218]: (m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_218))) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_218), u1_pre_topc(A_218))))) | ~v3_pre_topc(B_217, g1_pre_topc(u1_struct_0(A_218), u1_pre_topc(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_3350, plain, (![B_217]: (m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_217, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_3328])).
% 7.01/2.51  tff(c_3397, plain, (![B_220]: (m1_subset_1(B_220, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_220, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_220, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2699, c_112, c_111, c_2699, c_112, c_3350])).
% 7.01/2.51  tff(c_3431, plain, (![B_223]: (r1_tarski(B_223, k2_struct_0('#skF_2')) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_223, '#skF_3'))), inference(resolution, [status(thm)], [c_3397, c_12])).
% 7.01/2.51  tff(c_3448, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_3431])).
% 7.01/2.51  tff(c_3457, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3294, c_3448])).
% 7.01/2.51  tff(c_3459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3193, c_3457])).
% 7.01/2.51  tff(c_3460, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_3192])).
% 7.01/2.51  tff(c_3473, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3460, c_2699])).
% 7.01/2.51  tff(c_3474, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3460, c_112])).
% 7.01/2.51  tff(c_3938, plain, (![C_244, A_245]: (m1_pre_topc(C_244, A_245) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_244), u1_pre_topc(C_244)), A_245) | ~l1_pre_topc(C_244) | ~v2_pre_topc(C_244) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_244), u1_pre_topc(C_244))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_244), u1_pre_topc(C_244))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.01/2.51  tff(c_3944, plain, (![A_245]: (m1_pre_topc('#skF_2', A_245) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_245) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_245))), inference(superposition, [status(thm), theory('equality')], [c_3474, c_3938])).
% 7.01/2.51  tff(c_3958, plain, (![A_246]: (m1_pre_topc('#skF_2', A_246) | ~m1_pre_topc('#skF_3', A_246) | ~l1_pre_topc(A_246))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3473, c_3474, c_44, c_3473, c_3474, c_50, c_48, c_3473, c_3944])).
% 7.01/2.51  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_72, plain, (v1_tsep_1('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_91, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 7.01/2.51  tff(c_40, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.01/2.51  tff(c_924, plain, (![B_92, A_93]: (v3_pre_topc(u1_struct_0(B_92), A_93) | ~v1_tsep_1(B_92, A_93) | ~m1_subset_1(u1_struct_0(B_92), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.01/2.51  tff(c_2168, plain, (![B_150, A_151]: (v3_pre_topc(u1_struct_0(B_150), A_151) | ~v1_tsep_1(B_150, A_151) | ~v2_pre_topc(A_151) | ~m1_pre_topc(B_150, A_151) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_40, c_924])).
% 7.01/2.51  tff(c_2189, plain, (![A_151]: (v3_pre_topc(k2_struct_0('#skF_3'), A_151) | ~v1_tsep_1('#skF_3', A_151) | ~v2_pre_topc(A_151) | ~m1_pre_topc('#skF_3', A_151) | ~l1_pre_topc(A_151))), inference(superposition, [status(thm), theory('equality')], [c_111, c_2168])).
% 7.01/2.51  tff(c_56, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_114, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_92, c_56])).
% 7.01/2.51  tff(c_115, plain, (~v1_tsep_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_114])).
% 7.01/2.51  tff(c_124, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_42])).
% 7.01/2.51  tff(c_866, plain, (![C_89, A_90]: (m1_pre_topc(C_89, A_90) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_89), u1_pre_topc(C_89)), A_90) | ~l1_pre_topc(C_89) | ~v2_pre_topc(C_89) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_89), u1_pre_topc(C_89))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_89), u1_pre_topc(C_89))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.01/2.51  tff(c_869, plain, (![A_90]: (m1_pre_topc('#skF_2', A_90) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_90) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_90))), inference(superposition, [status(thm), theory('equality')], [c_112, c_866])).
% 7.01/2.51  tff(c_882, plain, (![A_91]: (m1_pre_topc('#skF_2', A_91) | ~m1_pre_topc('#skF_3', A_91) | ~l1_pre_topc(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_124, c_112, c_44, c_124, c_112, c_50, c_48, c_124, c_869])).
% 7.01/2.51  tff(c_110, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_100])).
% 7.01/2.51  tff(c_152, plain, (![B_47, A_48]: (m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.01/2.51  tff(c_173, plain, (![B_47]: (m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_47, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_152])).
% 7.01/2.51  tff(c_259, plain, (![B_55]: (m1_subset_1(u1_struct_0(B_55), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_55, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_173])).
% 7.01/2.51  tff(c_324, plain, (![B_58]: (r1_tarski(u1_struct_0(B_58), k2_struct_0('#skF_1')) | ~m1_pre_topc(B_58, '#skF_1'))), inference(resolution, [status(thm)], [c_259, c_12])).
% 7.01/2.51  tff(c_329, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_112, c_324])).
% 7.01/2.51  tff(c_340, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_329])).
% 7.01/2.51  tff(c_894, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_882, c_340])).
% 7.01/2.51  tff(c_910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_92, c_894])).
% 7.01/2.51  tff(c_912, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_329])).
% 7.01/2.51  tff(c_268, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_111, c_259])).
% 7.01/2.51  tff(c_274, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_268])).
% 7.01/2.51  tff(c_212, plain, (![B_51, A_52]: (v3_pre_topc(B_51, g1_pre_topc(u1_struct_0(A_52), u1_pre_topc(A_52))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~v3_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_215, plain, (![B_51]: (v3_pre_topc(B_51, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_51, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_212])).
% 7.01/2.51  tff(c_1103, plain, (![B_102]: (v3_pre_topc(B_102, '#skF_3') | ~m1_subset_1(B_102, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_102, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112, c_124, c_215])).
% 7.01/2.51  tff(c_1117, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_1103])).
% 7.01/2.51  tff(c_1118, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1117])).
% 7.01/2.51  tff(c_1121, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1118])).
% 7.01/2.51  tff(c_1125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1121])).
% 7.01/2.51  tff(c_1127, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_1117])).
% 7.01/2.51  tff(c_1073, plain, (![B_100, A_101]: (m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_101), u1_pre_topc(A_101))))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~v3_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_1087, plain, (![B_100]: (m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_100, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1073])).
% 7.01/2.51  tff(c_1269, plain, (![B_110]: (m1_subset_1(B_110, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_110, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_110, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112, c_111, c_124, c_1087])).
% 7.01/2.51  tff(c_1280, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_1269])).
% 7.01/2.51  tff(c_1285, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_1280])).
% 7.01/2.51  tff(c_1295, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1285, c_12])).
% 7.01/2.51  tff(c_1298, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1295, c_2])).
% 7.01/2.51  tff(c_1299, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1298])).
% 7.01/2.51  tff(c_1194, plain, (![B_107, A_108]: (v3_pre_topc(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_108), u1_pre_topc(A_108))))) | ~v3_pre_topc(B_107, g1_pre_topc(u1_struct_0(A_108), u1_pre_topc(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_1220, plain, (![B_107]: (v3_pre_topc(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_107, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1194])).
% 7.01/2.51  tff(c_1244, plain, (![B_109]: (v3_pre_topc(B_109, '#skF_2') | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_109, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_124, c_112, c_111, c_124, c_1220])).
% 7.01/2.51  tff(c_1258, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_1244])).
% 7.01/2.51  tff(c_1259, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1258])).
% 7.01/2.51  tff(c_1262, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1259])).
% 7.01/2.51  tff(c_1266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1262])).
% 7.01/2.51  tff(c_1268, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1258])).
% 7.01/2.51  tff(c_1300, plain, (![B_111, A_112]: (m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_112), u1_pre_topc(A_112))))) | ~v3_pre_topc(B_111, g1_pre_topc(u1_struct_0(A_112), u1_pre_topc(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_1326, plain, (![B_111]: (m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_111, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1300])).
% 7.01/2.51  tff(c_1387, plain, (![B_115]: (m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_115, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_124, c_112, c_111, c_124, c_112, c_1326])).
% 7.01/2.51  tff(c_1421, plain, (![B_118]: (r1_tarski(B_118, k2_struct_0('#skF_2')) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_118, '#skF_3'))), inference(resolution, [status(thm)], [c_1387, c_12])).
% 7.01/2.51  tff(c_1438, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_1421])).
% 7.01/2.51  tff(c_1447, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1268, c_1438])).
% 7.01/2.51  tff(c_1449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1299, c_1447])).
% 7.01/2.51  tff(c_1450, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1298])).
% 7.01/2.51  tff(c_1517, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_112])).
% 7.01/2.51  tff(c_280, plain, (![B_56, A_57]: (v1_tsep_1(B_56, A_57) | ~v3_pre_topc(u1_struct_0(B_56), A_57) | ~m1_subset_1(u1_struct_0(B_56), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.01/2.51  tff(c_304, plain, (![B_56]: (v1_tsep_1(B_56, '#skF_1') | ~v3_pre_topc(u1_struct_0(B_56), '#skF_1') | ~m1_subset_1(u1_struct_0(B_56), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_56, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_280])).
% 7.01/2.51  tff(c_2650, plain, (![B_176]: (v1_tsep_1(B_176, '#skF_1') | ~v3_pre_topc(u1_struct_0(B_176), '#skF_1') | ~m1_subset_1(u1_struct_0(B_176), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_176, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_304])).
% 7.01/2.51  tff(c_2653, plain, (v1_tsep_1('#skF_2', '#skF_1') | ~v3_pre_topc(u1_struct_0('#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_2650])).
% 7.01/2.51  tff(c_2667, plain, (v1_tsep_1('#skF_2', '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_912, c_274, c_1517, c_2653])).
% 7.01/2.51  tff(c_2668, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_115, c_2667])).
% 7.01/2.51  tff(c_2680, plain, (~v1_tsep_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2189, c_2668])).
% 7.01/2.51  tff(c_2687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_92, c_54, c_91, c_2680])).
% 7.01/2.51  tff(c_2688, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_114])).
% 7.01/2.51  tff(c_3970, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3958, c_2688])).
% 7.01/2.51  tff(c_3981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_92, c_3970])).
% 7.01/2.51  tff(c_3983, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 7.01/2.51  tff(c_64, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_3990, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3983, c_64])).
% 7.01/2.51  tff(c_3985, plain, (![A_247]: (u1_struct_0(A_247)=k2_struct_0(A_247) | ~l1_struct_0(A_247))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.01/2.51  tff(c_3991, plain, (![A_248]: (u1_struct_0(A_248)=k2_struct_0(A_248) | ~l1_pre_topc(A_248))), inference(resolution, [status(thm)], [c_18, c_3985])).
% 7.01/2.51  tff(c_4003, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3991])).
% 7.01/2.51  tff(c_4013, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4003, c_42])).
% 7.01/2.51  tff(c_4755, plain, (![C_298, A_299]: (m1_pre_topc(g1_pre_topc(u1_struct_0(C_298), u1_pre_topc(C_298)), A_299) | ~m1_pre_topc(C_298, A_299) | ~l1_pre_topc(C_298) | ~v2_pre_topc(C_298) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_298), u1_pre_topc(C_298))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_298), u1_pre_topc(C_298))) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.01/2.51  tff(c_4767, plain, (![A_299]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_299) | ~m1_pre_topc('#skF_2', A_299) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_299))), inference(superposition, [status(thm), theory('equality')], [c_4003, c_4755])).
% 7.01/2.51  tff(c_4789, plain, (![A_300]: (m1_pre_topc('#skF_3', A_300) | ~m1_pre_topc('#skF_2', A_300) | ~l1_pre_topc(A_300))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4013, c_4003, c_44, c_4013, c_4003, c_50, c_48, c_4013, c_4767])).
% 7.01/2.51  tff(c_4792, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3990, c_4789])).
% 7.01/2.51  tff(c_4795, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4792])).
% 7.01/2.51  tff(c_4797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3983, c_4795])).
% 7.01/2.51  tff(c_4799, plain, (~v1_tsep_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 7.01/2.51  tff(c_70, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.51  tff(c_4800, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_4799, c_70])).
% 7.01/2.51  tff(c_4798, plain, (v1_tsep_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 7.01/2.51  tff(c_4801, plain, (![A_301]: (u1_struct_0(A_301)=k2_struct_0(A_301) | ~l1_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.01/2.51  tff(c_4808, plain, (![A_302]: (u1_struct_0(A_302)=k2_struct_0(A_302) | ~l1_pre_topc(A_302))), inference(resolution, [status(thm)], [c_18, c_4801])).
% 7.01/2.51  tff(c_4820, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_4808])).
% 7.01/2.51  tff(c_4830, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4820, c_42])).
% 7.01/2.51  tff(c_4903, plain, (![B_313, A_314]: (v3_pre_topc(B_313, g1_pre_topc(u1_struct_0(A_314), u1_pre_topc(A_314))) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_314))) | ~v3_pre_topc(B_313, A_314) | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_4906, plain, (![B_313]: (v3_pre_topc(B_313, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_313, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4820, c_4903])).
% 7.01/2.51  tff(c_5772, plain, (![B_361]: (v3_pre_topc(B_361, '#skF_3') | ~m1_subset_1(B_361, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_361, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4820, c_4830, c_4906])).
% 7.01/2.51  tff(c_5786, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_5772])).
% 7.01/2.51  tff(c_5787, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_5786])).
% 7.01/2.51  tff(c_5790, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_5787])).
% 7.01/2.51  tff(c_5794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_5790])).
% 7.01/2.51  tff(c_5796, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_5786])).
% 7.01/2.51  tff(c_4819, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_4808])).
% 7.01/2.51  tff(c_5655, plain, (![B_354, A_355]: (m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_355), u1_pre_topc(A_355))))) | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0(A_355))) | ~v3_pre_topc(B_354, A_355) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_5669, plain, (![B_354]: (m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_354, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4820, c_5655])).
% 7.01/2.51  tff(c_6040, plain, (![B_374]: (m1_subset_1(B_374, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_374, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_374, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4820, c_4819, c_4830, c_5669])).
% 7.01/2.51  tff(c_6051, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_6040])).
% 7.01/2.51  tff(c_6056, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5796, c_6051])).
% 7.01/2.51  tff(c_6066, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6056, c_12])).
% 7.01/2.51  tff(c_6075, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6066, c_2])).
% 7.01/2.51  tff(c_6076, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_6075])).
% 7.01/2.51  tff(c_5797, plain, (![B_362, A_363]: (v3_pre_topc(B_362, A_363) | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_363), u1_pre_topc(A_363))))) | ~v3_pre_topc(B_362, g1_pre_topc(u1_struct_0(A_363), u1_pre_topc(A_363))) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_5807, plain, (![B_362]: (v3_pre_topc(B_362, '#skF_2') | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_362, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4820, c_5797])).
% 7.01/2.51  tff(c_5919, plain, (![B_368]: (v3_pre_topc(B_368, '#skF_2') | ~m1_subset_1(B_368, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_368, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4830, c_4820, c_4819, c_4830, c_5807])).
% 7.01/2.51  tff(c_5933, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_5919])).
% 7.01/2.51  tff(c_5934, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5933])).
% 7.01/2.51  tff(c_5937, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_5934])).
% 7.01/2.51  tff(c_5941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_5937])).
% 7.01/2.51  tff(c_5943, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_5933])).
% 7.01/2.51  tff(c_5944, plain, (![B_369, A_370]: (m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0(A_370))) | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_370), u1_pre_topc(A_370))))) | ~v3_pre_topc(B_369, g1_pre_topc(u1_struct_0(A_370), u1_pre_topc(A_370))) | ~l1_pre_topc(A_370) | ~v2_pre_topc(A_370))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.01/2.51  tff(c_5966, plain, (![B_369]: (m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_369, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4820, c_5944])).
% 7.01/2.51  tff(c_6109, plain, (![B_379]: (m1_subset_1(B_379, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_379, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_379, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4830, c_4820, c_4819, c_4830, c_4820, c_5966])).
% 7.01/2.51  tff(c_6134, plain, (![B_381]: (r1_tarski(B_381, k2_struct_0('#skF_2')) | ~m1_subset_1(B_381, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_381, '#skF_3'))), inference(resolution, [status(thm)], [c_6109, c_12])).
% 7.01/2.51  tff(c_6151, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_6134])).
% 7.01/2.51  tff(c_6160, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_6151])).
% 7.01/2.51  tff(c_6162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6076, c_6160])).
% 7.01/2.51  tff(c_6163, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_6075])).
% 7.01/2.51  tff(c_6180, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6163, c_4820])).
% 7.01/2.51  tff(c_4975, plain, (![B_318, A_319]: (v3_pre_topc(u1_struct_0(B_318), A_319) | ~v1_tsep_1(B_318, A_319) | ~m1_subset_1(u1_struct_0(B_318), k1_zfmisc_1(u1_struct_0(A_319))) | ~m1_pre_topc(B_318, A_319) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.01/2.51  tff(c_6782, plain, (![B_410, A_411]: (v3_pre_topc(u1_struct_0(B_410), A_411) | ~v1_tsep_1(B_410, A_411) | ~v2_pre_topc(A_411) | ~m1_pre_topc(B_410, A_411) | ~l1_pre_topc(A_411))), inference(resolution, [status(thm)], [c_40, c_4975])).
% 7.01/2.51  tff(c_6800, plain, (![A_411]: (v3_pre_topc(k2_struct_0('#skF_3'), A_411) | ~v1_tsep_1('#skF_2', A_411) | ~v2_pre_topc(A_411) | ~m1_pre_topc('#skF_2', A_411) | ~l1_pre_topc(A_411))), inference(superposition, [status(thm), theory('equality')], [c_6180, c_6782])).
% 7.01/2.51  tff(c_4818, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_4808])).
% 7.01/2.51  tff(c_4859, plain, (![B_310, A_311]: (m1_subset_1(u1_struct_0(B_310), k1_zfmisc_1(u1_struct_0(A_311))) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.01/2.51  tff(c_4880, plain, (![B_310]: (m1_subset_1(u1_struct_0(B_310), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_310, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4818, c_4859])).
% 7.01/2.51  tff(c_4935, plain, (![B_316]: (m1_subset_1(u1_struct_0(B_316), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_316, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4880])).
% 7.01/2.51  tff(c_4959, plain, (![B_317]: (r1_tarski(u1_struct_0(B_317), k2_struct_0('#skF_1')) | ~m1_pre_topc(B_317, '#skF_1'))), inference(resolution, [status(thm)], [c_4935, c_12])).
% 7.01/2.51  tff(c_4967, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_1')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4819, c_4959])).
% 7.01/2.51  tff(c_5016, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_4967])).
% 7.01/2.51  tff(c_5544, plain, (![C_347, A_348]: (m1_pre_topc(g1_pre_topc(u1_struct_0(C_347), u1_pre_topc(C_347)), A_348) | ~m1_pre_topc(C_347, A_348) | ~l1_pre_topc(C_347) | ~v2_pre_topc(C_347) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_347), u1_pre_topc(C_347))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_347), u1_pre_topc(C_347))) | ~l1_pre_topc(A_348))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.01/2.51  tff(c_5547, plain, (![A_348]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_348) | ~m1_pre_topc('#skF_2', A_348) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_348))), inference(superposition, [status(thm), theory('equality')], [c_4820, c_5544])).
% 7.01/2.51  tff(c_5560, plain, (![A_349]: (m1_pre_topc('#skF_3', A_349) | ~m1_pre_topc('#skF_2', A_349) | ~l1_pre_topc(A_349))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4830, c_4820, c_44, c_4830, c_4820, c_50, c_48, c_4830, c_5547])).
% 7.01/2.51  tff(c_5563, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4800, c_5560])).
% 7.01/2.51  tff(c_5566, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5563])).
% 7.01/2.51  tff(c_5568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5016, c_5566])).
% 7.01/2.51  tff(c_5570, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_4967])).
% 7.01/2.51  tff(c_4944, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4819, c_4935])).
% 7.01/2.51  tff(c_5647, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5570, c_4944])).
% 7.01/2.51  tff(c_5605, plain, (![B_352, A_353]: (v1_tsep_1(B_352, A_353) | ~v3_pre_topc(u1_struct_0(B_352), A_353) | ~m1_subset_1(u1_struct_0(B_352), k1_zfmisc_1(u1_struct_0(A_353))) | ~m1_pre_topc(B_352, A_353) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.01/2.51  tff(c_5629, plain, (![B_352]: (v1_tsep_1(B_352, '#skF_1') | ~v3_pre_topc(u1_struct_0(B_352), '#skF_1') | ~m1_subset_1(u1_struct_0(B_352), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_352, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4818, c_5605])).
% 7.01/2.51  tff(c_7218, plain, (![B_434]: (v1_tsep_1(B_434, '#skF_1') | ~v3_pre_topc(u1_struct_0(B_434), '#skF_1') | ~m1_subset_1(u1_struct_0(B_434), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_434, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5629])).
% 7.01/2.51  tff(c_7227, plain, (v1_tsep_1('#skF_3', '#skF_1') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4819, c_7218])).
% 7.01/2.51  tff(c_7238, plain, (v1_tsep_1('#skF_3', '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5570, c_5647, c_4819, c_7227])).
% 7.01/2.51  tff(c_7239, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_4799, c_7238])).
% 7.01/2.51  tff(c_7245, plain, (~v1_tsep_1('#skF_2', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6800, c_7239])).
% 7.01/2.51  tff(c_7252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_4800, c_54, c_4798, c_7245])).
% 7.01/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.51  
% 7.01/2.51  Inference rules
% 7.01/2.51  ----------------------
% 7.01/2.51  #Ref     : 0
% 7.01/2.51  #Sup     : 1462
% 7.01/2.51  #Fact    : 0
% 7.01/2.51  #Define  : 0
% 7.01/2.51  #Split   : 54
% 7.01/2.51  #Chain   : 0
% 7.01/2.51  #Close   : 0
% 7.01/2.51  
% 7.01/2.51  Ordering : KBO
% 7.01/2.51  
% 7.01/2.51  Simplification rules
% 7.01/2.51  ----------------------
% 7.01/2.51  #Subsume      : 475
% 7.01/2.51  #Demod        : 1797
% 7.01/2.51  #Tautology    : 354
% 7.01/2.51  #SimpNegUnit  : 23
% 7.01/2.51  #BackRed      : 46
% 7.01/2.51  
% 7.01/2.51  #Partial instantiations: 0
% 7.01/2.51  #Strategies tried      : 1
% 7.01/2.51  
% 7.01/2.51  Timing (in seconds)
% 7.01/2.51  ----------------------
% 7.01/2.51  Preprocessing        : 0.36
% 7.01/2.51  Parsing              : 0.19
% 7.01/2.51  CNF conversion       : 0.02
% 7.01/2.51  Main loop            : 1.28
% 7.01/2.51  Inferencing          : 0.42
% 7.01/2.51  Reduction            : 0.45
% 7.01/2.51  Demodulation         : 0.31
% 7.01/2.51  BG Simplification    : 0.05
% 7.01/2.51  Subsumption          : 0.26
% 7.01/2.51  Abstraction          : 0.06
% 7.01/2.51  MUC search           : 0.00
% 7.01/2.51  Cooper               : 0.00
% 7.01/2.51  Total                : 1.72
% 7.01/2.51  Index Insertion      : 0.00
% 7.01/2.51  Index Deletion       : 0.00
% 7.01/2.51  Index Matching       : 0.00
% 7.01/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
