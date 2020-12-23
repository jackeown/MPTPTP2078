%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:23 EST 2020

% Result     : Theorem 6.64s
% Output     : CNFRefutation 7.14s
% Verified   : 
% Statistics : Number of formulae       :  274 (3678 expanded)
%              Number of leaves         :   33 (1312 expanded)
%              Depth                    :   17
%              Number of atoms          :  642 (11595 expanded)
%              Number of equality atoms :   40 (1945 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v1_borsuk_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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
                 => ( ( v1_borsuk_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_borsuk_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).

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

tff(f_102,axiom,(
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

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_66,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
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

tff(c_2377,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_42])).

tff(c_2464,plain,(
    ! [B_181,A_182] :
      ( v3_pre_topc(B_181,g1_pre_topc(u1_struct_0(A_182),u1_pre_topc(A_182)))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ v3_pre_topc(B_181,A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2467,plain,(
    ! [B_181] :
      ( v3_pre_topc(B_181,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_181,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2464])).

tff(c_2741,plain,(
    ! [B_197] :
      ( v3_pre_topc(B_197,'#skF_3')
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_197,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_112,c_2377,c_2467])).

tff(c_2755,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_2741])).

tff(c_2756,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2755])).

tff(c_2759,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_2756])).

tff(c_2763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2759])).

tff(c_2765,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2755])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_111,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_100])).

tff(c_2766,plain,(
    ! [B_198,A_199] :
      ( m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_199),u1_pre_topc(A_199)))))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ v3_pre_topc(B_198,A_199)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2780,plain,(
    ! [B_198] :
      ( m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_198,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2766])).

tff(c_2848,plain,(
    ! [B_203] :
      ( m1_subset_1(B_203,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_203,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_203,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_112,c_111,c_2377,c_2780])).

tff(c_2859,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_2848])).

tff(c_2864,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2765,c_2859])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2868,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2864,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2871,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2868,c_2])).

tff(c_2872,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2871])).

tff(c_2887,plain,(
    ! [B_205,A_206] :
      ( v3_pre_topc(B_205,A_206)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_206),u1_pre_topc(A_206)))))
      | ~ v3_pre_topc(B_205,g1_pre_topc(u1_struct_0(A_206),u1_pre_topc(A_206)))
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2913,plain,(
    ! [B_205] :
      ( v3_pre_topc(B_205,'#skF_2')
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_205,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2887])).

tff(c_2937,plain,(
    ! [B_207] :
      ( v3_pre_topc(B_207,'#skF_2')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_207,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2377,c_112,c_111,c_2377,c_2913])).

tff(c_2957,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_2937])).

tff(c_2958,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2957])).

tff(c_2961,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2958])).

tff(c_2965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2961])).

tff(c_2967,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2957])).

tff(c_3025,plain,(
    ! [B_211,A_212] :
      ( m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_212),u1_pre_topc(A_212)))))
      | ~ v3_pre_topc(B_211,g1_pre_topc(u1_struct_0(A_212),u1_pre_topc(A_212)))
      | ~ l1_pre_topc(A_212)
      | ~ v2_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3051,plain,(
    ! [B_211] :
      ( m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_211,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_3025])).

tff(c_3096,plain,(
    ! [B_215] :
      ( m1_subset_1(B_215,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_215,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2377,c_112,c_111,c_2377,c_112,c_3051])).

tff(c_3109,plain,(
    ! [B_216] :
      ( r1_tarski(B_216,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_216,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3096,c_12])).

tff(c_3126,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_3109])).

tff(c_3135,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2967,c_3126])).

tff(c_3137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2872,c_3135])).

tff(c_3138,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2871])).

tff(c_3151,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3138,c_2377])).

tff(c_3152,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3138,c_112])).

tff(c_3605,plain,(
    ! [C_238,A_239] :
      ( m1_pre_topc(C_238,A_239)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_238),u1_pre_topc(C_238)),A_239)
      | ~ l1_pre_topc(C_238)
      | ~ v2_pre_topc(C_238)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_238),u1_pre_topc(C_238)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_238),u1_pre_topc(C_238)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3611,plain,(
    ! [A_239] :
      ( m1_pre_topc('#skF_2',A_239)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_239)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3152,c_3605])).

tff(c_3625,plain,(
    ! [A_240] :
      ( m1_pre_topc('#skF_2',A_240)
      | ~ m1_pre_topc('#skF_3',A_240)
      | ~ l1_pre_topc(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3151,c_3152,c_44,c_3151,c_3152,c_50,c_48,c_3151,c_3611])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_72,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_91,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_40,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_280,plain,(
    ! [B_56,A_57] :
      ( v4_pre_topc(u1_struct_0(B_56),A_57)
      | ~ v1_borsuk_1(B_56,A_57)
      | ~ m1_subset_1(u1_struct_0(B_56),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2079,plain,(
    ! [B_150,A_151] :
      ( v4_pre_topc(u1_struct_0(B_150),A_151)
      | ~ v1_borsuk_1(B_150,A_151)
      | ~ v2_pre_topc(A_151)
      | ~ m1_pre_topc(B_150,A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_40,c_280])).

tff(c_2088,plain,(
    ! [A_151] :
      ( v4_pre_topc(k2_struct_0('#skF_3'),A_151)
      | ~ v1_borsuk_1('#skF_3',A_151)
      | ~ v2_pre_topc(A_151)
      | ~ m1_pre_topc('#skF_3',A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_2079])).

tff(c_56,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_114,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_92,c_56])).

tff(c_115,plain,(
    ~ v1_borsuk_1('#skF_2','#skF_1') ),
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
    inference(cnfTransformation,[status(thm)],[f_102])).

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

tff(c_924,plain,(
    ! [B_92,A_93] :
      ( v1_borsuk_1(B_92,A_93)
      | ~ v4_pre_topc(u1_struct_0(B_92),A_93)
      | ~ m1_subset_1(u1_struct_0(B_92),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_948,plain,(
    ! [B_92] :
      ( v1_borsuk_1(B_92,'#skF_1')
      | ~ v4_pre_topc(u1_struct_0(B_92),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_92),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_92,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_924])).

tff(c_2329,plain,(
    ! [B_169] :
      ( v1_borsuk_1(B_169,'#skF_1')
      | ~ v4_pre_topc(u1_struct_0(B_169),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_169),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_169,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_948])).

tff(c_2332,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
    | ~ v4_pre_topc(u1_struct_0('#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_2329])).

tff(c_2346,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_274,c_1517,c_2332])).

tff(c_2347,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_2346])).

tff(c_2359,plain,
    ( ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2088,c_2347])).

tff(c_2366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_92,c_54,c_91,c_2359])).

tff(c_2367,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_3643,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3625,c_2367])).

tff(c_3660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_92,c_3643])).

tff(c_3662,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3669,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3662,c_64])).

tff(c_3664,plain,(
    ! [A_241] :
      ( u1_struct_0(A_241) = k2_struct_0(A_241)
      | ~ l1_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3670,plain,(
    ! [A_242] :
      ( u1_struct_0(A_242) = k2_struct_0(A_242)
      | ~ l1_pre_topc(A_242) ) ),
    inference(resolution,[status(thm)],[c_18,c_3664])).

tff(c_3682,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3670])).

tff(c_3692,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3682,c_42])).

tff(c_4434,plain,(
    ! [C_292,A_293] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_292),u1_pre_topc(C_292)),A_293)
      | ~ m1_pre_topc(C_292,A_293)
      | ~ l1_pre_topc(C_292)
      | ~ v2_pre_topc(C_292)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_292),u1_pre_topc(C_292)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_292),u1_pre_topc(C_292)))
      | ~ l1_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4446,plain,(
    ! [A_293] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_293)
      | ~ m1_pre_topc('#skF_2',A_293)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3682,c_4434])).

tff(c_4468,plain,(
    ! [A_294] :
      ( m1_pre_topc('#skF_3',A_294)
      | ~ m1_pre_topc('#skF_2',A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3692,c_3682,c_44,c_3692,c_3682,c_50,c_48,c_3692,c_4446])).

tff(c_4471,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3669,c_4468])).

tff(c_4474,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4471])).

tff(c_4476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3662,c_4474])).

tff(c_4478,plain,(
    ~ v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4480,plain,(
    ! [A_295] :
      ( u1_struct_0(A_295) = k2_struct_0(A_295)
      | ~ l1_struct_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4487,plain,(
    ! [A_296] :
      ( u1_struct_0(A_296) = k2_struct_0(A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(resolution,[status(thm)],[c_18,c_4480])).

tff(c_4498,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_4487])).

tff(c_4497,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_4487])).

tff(c_4538,plain,(
    ! [B_304,A_305] :
      ( m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ m1_pre_topc(B_304,A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4559,plain,(
    ! [B_304] :
      ( m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_304,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4497,c_4538])).

tff(c_4614,plain,(
    ! [B_310] :
      ( m1_subset_1(u1_struct_0(B_310),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_310,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4559])).

tff(c_4638,plain,(
    ! [B_311] :
      ( r1_tarski(u1_struct_0(B_311),k2_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_311,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4614,c_12])).

tff(c_4646,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4498,c_4638])).

tff(c_4695,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4646])).

tff(c_70,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4479,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_4478,c_70])).

tff(c_4499,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_4487])).

tff(c_4509,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4499,c_42])).

tff(c_4582,plain,(
    ! [B_307,A_308] :
      ( v3_pre_topc(B_307,g1_pre_topc(u1_struct_0(A_308),u1_pre_topc(A_308)))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ v3_pre_topc(B_307,A_308)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4585,plain,(
    ! [B_307] :
      ( v3_pre_topc(B_307,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_307,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_4582])).

tff(c_4885,plain,(
    ! [B_325] :
      ( v3_pre_topc(B_325,'#skF_3')
      | ~ m1_subset_1(B_325,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_325,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4499,c_4509,c_4585])).

tff(c_4899,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_4885])).

tff(c_4900,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4899])).

tff(c_4923,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_4900])).

tff(c_4927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4923])).

tff(c_4929,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4899])).

tff(c_4835,plain,(
    ! [B_322,A_323] :
      ( m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_323),u1_pre_topc(A_323)))))
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ v3_pre_topc(B_322,A_323)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4849,plain,(
    ! [B_322] :
      ( m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_322,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_4835])).

tff(c_5067,plain,(
    ! [B_334] :
      ( m1_subset_1(B_334,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_334,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_334,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4499,c_4498,c_4509,c_4849])).

tff(c_5078,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_5067])).

tff(c_5083,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_5078])).

tff(c_5093,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5083,c_12])).

tff(c_5096,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5093,c_2])).

tff(c_5157,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5096])).

tff(c_4962,plain,(
    ! [B_329,A_330] :
      ( v3_pre_topc(B_329,A_330)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_330),u1_pre_topc(A_330)))))
      | ~ v3_pre_topc(B_329,g1_pre_topc(u1_struct_0(A_330),u1_pre_topc(A_330)))
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4976,plain,(
    ! [B_329] :
      ( v3_pre_topc(B_329,'#skF_2')
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_329,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_4962])).

tff(c_5052,plain,(
    ! [B_333] :
      ( v3_pre_topc(B_333,'#skF_2')
      | ~ m1_subset_1(B_333,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_333,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4509,c_4499,c_4498,c_4509,c_4976])).

tff(c_5066,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_5052])).

tff(c_5097,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5066])).

tff(c_5100,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_5097])).

tff(c_5104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_5100])).

tff(c_5106,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5066])).

tff(c_5107,plain,(
    ! [B_335,A_336] :
      ( m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_336),u1_pre_topc(A_336)))))
      | ~ v3_pre_topc(B_335,g1_pre_topc(u1_struct_0(A_336),u1_pre_topc(A_336)))
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5129,plain,(
    ! [B_335] :
      ( m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_335,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_5107])).

tff(c_5158,plain,(
    ! [B_337] :
      ( m1_subset_1(B_337,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_337,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_337,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4509,c_4499,c_4498,c_4509,c_4499,c_5129])).

tff(c_5287,plain,(
    ! [B_347] :
      ( r1_tarski(B_347,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_347,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_347,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5158,c_12])).

tff(c_5304,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_5287])).

tff(c_5313,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5106,c_5304])).

tff(c_5315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5157,c_5313])).

tff(c_5316,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5096])).

tff(c_5332,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5316,c_4509])).

tff(c_5333,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5316,c_4499])).

tff(c_5510,plain,(
    ! [C_352,A_353] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_352),u1_pre_topc(C_352)),A_353)
      | ~ m1_pre_topc(C_352,A_353)
      | ~ l1_pre_topc(C_352)
      | ~ v2_pre_topc(C_352)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_352),u1_pre_topc(C_352)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_352),u1_pre_topc(C_352)))
      | ~ l1_pre_topc(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5516,plain,(
    ! [A_353] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_353)
      | ~ m1_pre_topc('#skF_2',A_353)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5333,c_5510])).

tff(c_5530,plain,(
    ! [A_354] :
      ( m1_pre_topc('#skF_3',A_354)
      | ~ m1_pre_topc('#skF_2',A_354)
      | ~ l1_pre_topc(A_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5332,c_5333,c_44,c_5332,c_5333,c_50,c_48,c_5332,c_5516])).

tff(c_5533,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4479,c_5530])).

tff(c_5536,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5533])).

tff(c_5538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4695,c_5536])).

tff(c_5540,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4646])).

tff(c_4623,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4498,c_4614])).

tff(c_5617,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5540,c_4623])).

tff(c_4477,plain,(
    v1_borsuk_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_5742,plain,(
    ! [B_366] :
      ( v3_pre_topc(B_366,'#skF_3')
      | ~ m1_subset_1(B_366,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_366,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4499,c_4509,c_4585])).

tff(c_5756,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_5742])).

tff(c_5757,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5756])).

tff(c_5760,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_5757])).

tff(c_5764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_5760])).

tff(c_5766,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_5756])).

tff(c_5625,plain,(
    ! [B_359,A_360] :
      ( m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_360),u1_pre_topc(A_360)))))
      | ~ m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ v3_pre_topc(B_359,A_360)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5639,plain,(
    ! [B_359] :
      ( m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_359,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_5625])).

tff(c_6010,plain,(
    ! [B_379] :
      ( m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_379,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4499,c_4498,c_4509,c_5639])).

tff(c_6021,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_6010])).

tff(c_6026,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5766,c_6021])).

tff(c_6036,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6026,c_12])).

tff(c_6045,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6036,c_2])).

tff(c_6046,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6045])).

tff(c_5767,plain,(
    ! [B_367,A_368] :
      ( v3_pre_topc(B_367,A_368)
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_368),u1_pre_topc(A_368)))))
      | ~ v3_pre_topc(B_367,g1_pre_topc(u1_struct_0(A_368),u1_pre_topc(A_368)))
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5777,plain,(
    ! [B_367] :
      ( v3_pre_topc(B_367,'#skF_2')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_367,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_5767])).

tff(c_5889,plain,(
    ! [B_373] :
      ( v3_pre_topc(B_373,'#skF_2')
      | ~ m1_subset_1(B_373,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_373,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4509,c_4499,c_4498,c_4509,c_5777])).

tff(c_5903,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_5889])).

tff(c_5904,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5903])).

tff(c_5907,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_5904])).

tff(c_5911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_5907])).

tff(c_5913,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5903])).

tff(c_5914,plain,(
    ! [B_374,A_375] :
      ( m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_375),u1_pre_topc(A_375)))))
      | ~ v3_pre_topc(B_374,g1_pre_topc(u1_struct_0(A_375),u1_pre_topc(A_375)))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5936,plain,(
    ! [B_374] :
      ( m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_374,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_5914])).

tff(c_6070,plain,(
    ! [B_383] :
      ( m1_subset_1(B_383,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_383,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_383,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4509,c_4499,c_4498,c_4509,c_4499,c_5936])).

tff(c_6104,plain,(
    ! [B_386] :
      ( r1_tarski(B_386,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_386,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6070,c_12])).

tff(c_6121,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_6104])).

tff(c_6130,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5913,c_6121])).

tff(c_6132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6046,c_6130])).

tff(c_6133,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6045])).

tff(c_6150,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6133,c_4499])).

tff(c_5575,plain,(
    ! [B_357,A_358] :
      ( v4_pre_topc(u1_struct_0(B_357),A_358)
      | ~ v1_borsuk_1(B_357,A_358)
      | ~ m1_subset_1(u1_struct_0(B_357),k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ m1_pre_topc(B_357,A_358)
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5599,plain,(
    ! [B_357] :
      ( v4_pre_topc(u1_struct_0(B_357),'#skF_1')
      | ~ v1_borsuk_1(B_357,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_357),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_357,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4497,c_5575])).

tff(c_6843,plain,(
    ! [B_428] :
      ( v4_pre_topc(u1_struct_0(B_428),'#skF_1')
      | ~ v1_borsuk_1(B_428,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_428),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_428,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5599])).

tff(c_6846,plain,
    ( v4_pre_topc(u1_struct_0('#skF_2'),'#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6150,c_6843])).

tff(c_6860,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4479,c_5617,c_4477,c_6150,c_6846])).

tff(c_4654,plain,(
    ! [B_312,A_313] :
      ( v1_borsuk_1(B_312,A_313)
      | ~ v4_pre_topc(u1_struct_0(B_312),A_313)
      | ~ m1_subset_1(u1_struct_0(B_312),k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ m1_pre_topc(B_312,A_313)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6676,plain,(
    ! [B_413,A_414] :
      ( v1_borsuk_1(B_413,A_414)
      | ~ v4_pre_topc(u1_struct_0(B_413),A_414)
      | ~ v2_pre_topc(A_414)
      | ~ m1_pre_topc(B_413,A_414)
      | ~ l1_pre_topc(A_414) ) ),
    inference(resolution,[status(thm)],[c_40,c_4654])).

tff(c_6685,plain,(
    ! [A_414] :
      ( v1_borsuk_1('#skF_3',A_414)
      | ~ v4_pre_topc(k2_struct_0('#skF_3'),A_414)
      | ~ v2_pre_topc(A_414)
      | ~ m1_pre_topc('#skF_3',A_414)
      | ~ l1_pre_topc(A_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4498,c_6676])).

tff(c_6872,plain,
    ( v1_borsuk_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6860,c_6685])).

tff(c_6878,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5540,c_54,c_6872])).

tff(c_6880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4478,c_6878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:01:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.64/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.36  
% 6.64/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.36  %$ v4_pre_topc > v3_pre_topc > v1_borsuk_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.64/2.36  
% 6.64/2.36  %Foreground sorts:
% 6.64/2.36  
% 6.64/2.36  
% 6.64/2.36  %Background operators:
% 6.64/2.36  
% 6.64/2.36  
% 6.64/2.36  %Foreground operators:
% 6.64/2.36  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.64/2.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.64/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.64/2.36  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.64/2.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.64/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.64/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.64/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.64/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.64/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.64/2.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.64/2.36  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.64/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.64/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.64/2.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.64/2.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.64/2.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.64/2.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.64/2.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.64/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.64/2.36  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 6.64/2.36  
% 7.14/2.40  tff(f_134, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> (v1_borsuk_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tmap_1)).
% 7.14/2.40  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 7.14/2.40  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.14/2.40  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.14/2.40  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.14/2.40  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.14/2.40  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 7.14/2.40  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.14/2.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.14/2.40  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 7.14/2.40  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.14/2.40  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 7.14/2.40  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_66, plain, (v1_borsuk_1('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_92, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 7.14/2.40  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_28, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.14/2.40  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.14/2.40  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.14/2.40  tff(c_73, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 7.14/2.40  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.14/2.40  tff(c_94, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.14/2.40  tff(c_100, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_18, c_94])).
% 7.14/2.40  tff(c_112, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_100])).
% 7.14/2.40  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_2377, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_42])).
% 7.14/2.40  tff(c_2464, plain, (![B_181, A_182]: (v3_pre_topc(B_181, g1_pre_topc(u1_struct_0(A_182), u1_pre_topc(A_182))) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_182))) | ~v3_pre_topc(B_181, A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_2467, plain, (![B_181]: (v3_pre_topc(B_181, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_181, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2464])).
% 7.14/2.40  tff(c_2741, plain, (![B_197]: (v3_pre_topc(B_197, '#skF_3') | ~m1_subset_1(B_197, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_197, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112, c_2377, c_2467])).
% 7.14/2.40  tff(c_2755, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_2741])).
% 7.14/2.40  tff(c_2756, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_2755])).
% 7.14/2.40  tff(c_2759, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_2756])).
% 7.14/2.40  tff(c_2763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2759])).
% 7.14/2.40  tff(c_2765, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_2755])).
% 7.14/2.40  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_111, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_100])).
% 7.14/2.40  tff(c_2766, plain, (![B_198, A_199]: (m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_199), u1_pre_topc(A_199))))) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_199))) | ~v3_pre_topc(B_198, A_199) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_2780, plain, (![B_198]: (m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_198, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2766])).
% 7.14/2.40  tff(c_2848, plain, (![B_203]: (m1_subset_1(B_203, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_203, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_203, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112, c_111, c_2377, c_2780])).
% 7.14/2.40  tff(c_2859, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_2848])).
% 7.14/2.40  tff(c_2864, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2765, c_2859])).
% 7.14/2.40  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.14/2.40  tff(c_2868, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2864, c_12])).
% 7.14/2.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.14/2.40  tff(c_2871, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2868, c_2])).
% 7.14/2.40  tff(c_2872, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2871])).
% 7.14/2.40  tff(c_2887, plain, (![B_205, A_206]: (v3_pre_topc(B_205, A_206) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_206), u1_pre_topc(A_206))))) | ~v3_pre_topc(B_205, g1_pre_topc(u1_struct_0(A_206), u1_pre_topc(A_206))) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_2913, plain, (![B_205]: (v3_pre_topc(B_205, '#skF_2') | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_205, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2887])).
% 7.14/2.40  tff(c_2937, plain, (![B_207]: (v3_pre_topc(B_207, '#skF_2') | ~m1_subset_1(B_207, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_207, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2377, c_112, c_111, c_2377, c_2913])).
% 7.14/2.40  tff(c_2957, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_2937])).
% 7.14/2.40  tff(c_2958, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2957])).
% 7.14/2.40  tff(c_2961, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_2958])).
% 7.14/2.40  tff(c_2965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2961])).
% 7.14/2.40  tff(c_2967, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_2957])).
% 7.14/2.40  tff(c_3025, plain, (![B_211, A_212]: (m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_212))) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_212), u1_pre_topc(A_212))))) | ~v3_pre_topc(B_211, g1_pre_topc(u1_struct_0(A_212), u1_pre_topc(A_212))) | ~l1_pre_topc(A_212) | ~v2_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_3051, plain, (![B_211]: (m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_211, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_3025])).
% 7.14/2.40  tff(c_3096, plain, (![B_215]: (m1_subset_1(B_215, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_215, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2377, c_112, c_111, c_2377, c_112, c_3051])).
% 7.14/2.40  tff(c_3109, plain, (![B_216]: (r1_tarski(B_216, k2_struct_0('#skF_2')) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_216, '#skF_3'))), inference(resolution, [status(thm)], [c_3096, c_12])).
% 7.14/2.40  tff(c_3126, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_3109])).
% 7.14/2.40  tff(c_3135, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2967, c_3126])).
% 7.14/2.40  tff(c_3137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2872, c_3135])).
% 7.14/2.40  tff(c_3138, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_2871])).
% 7.14/2.40  tff(c_3151, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3138, c_2377])).
% 7.14/2.40  tff(c_3152, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3138, c_112])).
% 7.14/2.40  tff(c_3605, plain, (![C_238, A_239]: (m1_pre_topc(C_238, A_239) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_238), u1_pre_topc(C_238)), A_239) | ~l1_pre_topc(C_238) | ~v2_pre_topc(C_238) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_238), u1_pre_topc(C_238))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_238), u1_pre_topc(C_238))) | ~l1_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.14/2.40  tff(c_3611, plain, (![A_239]: (m1_pre_topc('#skF_2', A_239) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_239) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_239))), inference(superposition, [status(thm), theory('equality')], [c_3152, c_3605])).
% 7.14/2.40  tff(c_3625, plain, (![A_240]: (m1_pre_topc('#skF_2', A_240) | ~m1_pre_topc('#skF_3', A_240) | ~l1_pre_topc(A_240))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3151, c_3152, c_44, c_3151, c_3152, c_50, c_48, c_3151, c_3611])).
% 7.14/2.40  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_72, plain, (v1_borsuk_1('#skF_2', '#skF_1') | v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_91, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 7.14/2.40  tff(c_40, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.14/2.40  tff(c_280, plain, (![B_56, A_57]: (v4_pre_topc(u1_struct_0(B_56), A_57) | ~v1_borsuk_1(B_56, A_57) | ~m1_subset_1(u1_struct_0(B_56), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.14/2.40  tff(c_2079, plain, (![B_150, A_151]: (v4_pre_topc(u1_struct_0(B_150), A_151) | ~v1_borsuk_1(B_150, A_151) | ~v2_pre_topc(A_151) | ~m1_pre_topc(B_150, A_151) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_40, c_280])).
% 7.14/2.40  tff(c_2088, plain, (![A_151]: (v4_pre_topc(k2_struct_0('#skF_3'), A_151) | ~v1_borsuk_1('#skF_3', A_151) | ~v2_pre_topc(A_151) | ~m1_pre_topc('#skF_3', A_151) | ~l1_pre_topc(A_151))), inference(superposition, [status(thm), theory('equality')], [c_111, c_2079])).
% 7.14/2.40  tff(c_56, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_114, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_92, c_56])).
% 7.14/2.40  tff(c_115, plain, (~v1_borsuk_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_114])).
% 7.14/2.40  tff(c_124, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_42])).
% 7.14/2.40  tff(c_866, plain, (![C_89, A_90]: (m1_pre_topc(C_89, A_90) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_89), u1_pre_topc(C_89)), A_90) | ~l1_pre_topc(C_89) | ~v2_pre_topc(C_89) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_89), u1_pre_topc(C_89))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_89), u1_pre_topc(C_89))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.14/2.40  tff(c_869, plain, (![A_90]: (m1_pre_topc('#skF_2', A_90) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_90) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_90))), inference(superposition, [status(thm), theory('equality')], [c_112, c_866])).
% 7.14/2.40  tff(c_882, plain, (![A_91]: (m1_pre_topc('#skF_2', A_91) | ~m1_pre_topc('#skF_3', A_91) | ~l1_pre_topc(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_124, c_112, c_44, c_124, c_112, c_50, c_48, c_124, c_869])).
% 7.14/2.40  tff(c_110, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_100])).
% 7.14/2.40  tff(c_152, plain, (![B_47, A_48]: (m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.14/2.40  tff(c_173, plain, (![B_47]: (m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_47, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_152])).
% 7.14/2.40  tff(c_259, plain, (![B_55]: (m1_subset_1(u1_struct_0(B_55), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_55, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_173])).
% 7.14/2.40  tff(c_324, plain, (![B_58]: (r1_tarski(u1_struct_0(B_58), k2_struct_0('#skF_1')) | ~m1_pre_topc(B_58, '#skF_1'))), inference(resolution, [status(thm)], [c_259, c_12])).
% 7.14/2.40  tff(c_329, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_112, c_324])).
% 7.14/2.40  tff(c_340, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_329])).
% 7.14/2.40  tff(c_894, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_882, c_340])).
% 7.14/2.40  tff(c_910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_92, c_894])).
% 7.14/2.40  tff(c_912, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_329])).
% 7.14/2.40  tff(c_268, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_111, c_259])).
% 7.14/2.40  tff(c_274, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_268])).
% 7.14/2.40  tff(c_212, plain, (![B_51, A_52]: (v3_pre_topc(B_51, g1_pre_topc(u1_struct_0(A_52), u1_pre_topc(A_52))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~v3_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_215, plain, (![B_51]: (v3_pre_topc(B_51, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_51, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_212])).
% 7.14/2.40  tff(c_1103, plain, (![B_102]: (v3_pre_topc(B_102, '#skF_3') | ~m1_subset_1(B_102, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_102, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112, c_124, c_215])).
% 7.14/2.40  tff(c_1117, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_1103])).
% 7.14/2.40  tff(c_1118, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1117])).
% 7.14/2.40  tff(c_1121, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1118])).
% 7.14/2.40  tff(c_1125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1121])).
% 7.14/2.40  tff(c_1127, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_1117])).
% 7.14/2.40  tff(c_1073, plain, (![B_100, A_101]: (m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_101), u1_pre_topc(A_101))))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~v3_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_1087, plain, (![B_100]: (m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_100, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1073])).
% 7.14/2.40  tff(c_1269, plain, (![B_110]: (m1_subset_1(B_110, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_110, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_110, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112, c_111, c_124, c_1087])).
% 7.14/2.40  tff(c_1280, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_1269])).
% 7.14/2.40  tff(c_1285, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_1280])).
% 7.14/2.40  tff(c_1295, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1285, c_12])).
% 7.14/2.40  tff(c_1298, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1295, c_2])).
% 7.14/2.40  tff(c_1299, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1298])).
% 7.14/2.40  tff(c_1194, plain, (![B_107, A_108]: (v3_pre_topc(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_108), u1_pre_topc(A_108))))) | ~v3_pre_topc(B_107, g1_pre_topc(u1_struct_0(A_108), u1_pre_topc(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_1220, plain, (![B_107]: (v3_pre_topc(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_107, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1194])).
% 7.14/2.40  tff(c_1244, plain, (![B_109]: (v3_pre_topc(B_109, '#skF_2') | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_109, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_124, c_112, c_111, c_124, c_1220])).
% 7.14/2.40  tff(c_1258, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_1244])).
% 7.14/2.40  tff(c_1259, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1258])).
% 7.14/2.40  tff(c_1262, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1259])).
% 7.14/2.40  tff(c_1266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1262])).
% 7.14/2.40  tff(c_1268, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1258])).
% 7.14/2.40  tff(c_1300, plain, (![B_111, A_112]: (m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_112), u1_pre_topc(A_112))))) | ~v3_pre_topc(B_111, g1_pre_topc(u1_struct_0(A_112), u1_pre_topc(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_1326, plain, (![B_111]: (m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_111, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1300])).
% 7.14/2.40  tff(c_1387, plain, (![B_115]: (m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_115, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_124, c_112, c_111, c_124, c_112, c_1326])).
% 7.14/2.40  tff(c_1421, plain, (![B_118]: (r1_tarski(B_118, k2_struct_0('#skF_2')) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_118, '#skF_3'))), inference(resolution, [status(thm)], [c_1387, c_12])).
% 7.14/2.40  tff(c_1438, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_1421])).
% 7.14/2.40  tff(c_1447, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1268, c_1438])).
% 7.14/2.40  tff(c_1449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1299, c_1447])).
% 7.14/2.40  tff(c_1450, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1298])).
% 7.14/2.40  tff(c_1517, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_112])).
% 7.14/2.40  tff(c_924, plain, (![B_92, A_93]: (v1_borsuk_1(B_92, A_93) | ~v4_pre_topc(u1_struct_0(B_92), A_93) | ~m1_subset_1(u1_struct_0(B_92), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.14/2.40  tff(c_948, plain, (![B_92]: (v1_borsuk_1(B_92, '#skF_1') | ~v4_pre_topc(u1_struct_0(B_92), '#skF_1') | ~m1_subset_1(u1_struct_0(B_92), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_92, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_924])).
% 7.14/2.40  tff(c_2329, plain, (![B_169]: (v1_borsuk_1(B_169, '#skF_1') | ~v4_pre_topc(u1_struct_0(B_169), '#skF_1') | ~m1_subset_1(u1_struct_0(B_169), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_169, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_948])).
% 7.14/2.40  tff(c_2332, plain, (v1_borsuk_1('#skF_2', '#skF_1') | ~v4_pre_topc(u1_struct_0('#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_2329])).
% 7.14/2.40  tff(c_2346, plain, (v1_borsuk_1('#skF_2', '#skF_1') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_912, c_274, c_1517, c_2332])).
% 7.14/2.40  tff(c_2347, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_115, c_2346])).
% 7.14/2.40  tff(c_2359, plain, (~v1_borsuk_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2088, c_2347])).
% 7.14/2.40  tff(c_2366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_92, c_54, c_91, c_2359])).
% 7.14/2.40  tff(c_2367, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_114])).
% 7.14/2.40  tff(c_3643, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3625, c_2367])).
% 7.14/2.40  tff(c_3660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_92, c_3643])).
% 7.14/2.40  tff(c_3662, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 7.14/2.40  tff(c_64, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_3669, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3662, c_64])).
% 7.14/2.40  tff(c_3664, plain, (![A_241]: (u1_struct_0(A_241)=k2_struct_0(A_241) | ~l1_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.14/2.40  tff(c_3670, plain, (![A_242]: (u1_struct_0(A_242)=k2_struct_0(A_242) | ~l1_pre_topc(A_242))), inference(resolution, [status(thm)], [c_18, c_3664])).
% 7.14/2.40  tff(c_3682, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3670])).
% 7.14/2.40  tff(c_3692, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3682, c_42])).
% 7.14/2.40  tff(c_4434, plain, (![C_292, A_293]: (m1_pre_topc(g1_pre_topc(u1_struct_0(C_292), u1_pre_topc(C_292)), A_293) | ~m1_pre_topc(C_292, A_293) | ~l1_pre_topc(C_292) | ~v2_pre_topc(C_292) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_292), u1_pre_topc(C_292))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_292), u1_pre_topc(C_292))) | ~l1_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.14/2.40  tff(c_4446, plain, (![A_293]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_293) | ~m1_pre_topc('#skF_2', A_293) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_293))), inference(superposition, [status(thm), theory('equality')], [c_3682, c_4434])).
% 7.14/2.40  tff(c_4468, plain, (![A_294]: (m1_pre_topc('#skF_3', A_294) | ~m1_pre_topc('#skF_2', A_294) | ~l1_pre_topc(A_294))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3692, c_3682, c_44, c_3692, c_3682, c_50, c_48, c_3692, c_4446])).
% 7.14/2.40  tff(c_4471, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3669, c_4468])).
% 7.14/2.40  tff(c_4474, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4471])).
% 7.14/2.40  tff(c_4476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3662, c_4474])).
% 7.14/2.40  tff(c_4478, plain, (~v1_borsuk_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 7.14/2.40  tff(c_4480, plain, (![A_295]: (u1_struct_0(A_295)=k2_struct_0(A_295) | ~l1_struct_0(A_295))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.14/2.40  tff(c_4487, plain, (![A_296]: (u1_struct_0(A_296)=k2_struct_0(A_296) | ~l1_pre_topc(A_296))), inference(resolution, [status(thm)], [c_18, c_4480])).
% 7.14/2.40  tff(c_4498, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_4487])).
% 7.14/2.40  tff(c_4497, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_4487])).
% 7.14/2.40  tff(c_4538, plain, (![B_304, A_305]: (m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(u1_struct_0(A_305))) | ~m1_pre_topc(B_304, A_305) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.14/2.40  tff(c_4559, plain, (![B_304]: (m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_304, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4497, c_4538])).
% 7.14/2.40  tff(c_4614, plain, (![B_310]: (m1_subset_1(u1_struct_0(B_310), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_310, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4559])).
% 7.14/2.40  tff(c_4638, plain, (![B_311]: (r1_tarski(u1_struct_0(B_311), k2_struct_0('#skF_1')) | ~m1_pre_topc(B_311, '#skF_1'))), inference(resolution, [status(thm)], [c_4614, c_12])).
% 7.14/2.40  tff(c_4646, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_1')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4498, c_4638])).
% 7.14/2.40  tff(c_4695, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_4646])).
% 7.14/2.40  tff(c_70, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.14/2.40  tff(c_4479, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_4478, c_70])).
% 7.14/2.40  tff(c_4499, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_4487])).
% 7.14/2.40  tff(c_4509, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4499, c_42])).
% 7.14/2.40  tff(c_4582, plain, (![B_307, A_308]: (v3_pre_topc(B_307, g1_pre_topc(u1_struct_0(A_308), u1_pre_topc(A_308))) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_308))) | ~v3_pre_topc(B_307, A_308) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_4585, plain, (![B_307]: (v3_pre_topc(B_307, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_307, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_4582])).
% 7.14/2.40  tff(c_4885, plain, (![B_325]: (v3_pre_topc(B_325, '#skF_3') | ~m1_subset_1(B_325, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_325, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4499, c_4509, c_4585])).
% 7.14/2.40  tff(c_4899, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_4885])).
% 7.14/2.40  tff(c_4900, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_4899])).
% 7.14/2.40  tff(c_4923, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_4900])).
% 7.14/2.40  tff(c_4927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4923])).
% 7.14/2.40  tff(c_4929, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_4899])).
% 7.14/2.40  tff(c_4835, plain, (![B_322, A_323]: (m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_323), u1_pre_topc(A_323))))) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(A_323))) | ~v3_pre_topc(B_322, A_323) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_4849, plain, (![B_322]: (m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_322, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_4835])).
% 7.14/2.40  tff(c_5067, plain, (![B_334]: (m1_subset_1(B_334, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_334, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_334, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4499, c_4498, c_4509, c_4849])).
% 7.14/2.40  tff(c_5078, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_5067])).
% 7.14/2.40  tff(c_5083, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4929, c_5078])).
% 7.14/2.40  tff(c_5093, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_5083, c_12])).
% 7.14/2.40  tff(c_5096, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_5093, c_2])).
% 7.14/2.40  tff(c_5157, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_5096])).
% 7.14/2.40  tff(c_4962, plain, (![B_329, A_330]: (v3_pre_topc(B_329, A_330) | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_330), u1_pre_topc(A_330))))) | ~v3_pre_topc(B_329, g1_pre_topc(u1_struct_0(A_330), u1_pre_topc(A_330))) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_4976, plain, (![B_329]: (v3_pre_topc(B_329, '#skF_2') | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_329, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_4962])).
% 7.14/2.40  tff(c_5052, plain, (![B_333]: (v3_pre_topc(B_333, '#skF_2') | ~m1_subset_1(B_333, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_333, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4509, c_4499, c_4498, c_4509, c_4976])).
% 7.14/2.40  tff(c_5066, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_5052])).
% 7.14/2.40  tff(c_5097, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5066])).
% 7.14/2.40  tff(c_5100, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_5097])).
% 7.14/2.40  tff(c_5104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_5100])).
% 7.14/2.40  tff(c_5106, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_5066])).
% 7.14/2.40  tff(c_5107, plain, (![B_335, A_336]: (m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_336))) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_336), u1_pre_topc(A_336))))) | ~v3_pre_topc(B_335, g1_pre_topc(u1_struct_0(A_336), u1_pre_topc(A_336))) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_5129, plain, (![B_335]: (m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_335, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_5107])).
% 7.14/2.40  tff(c_5158, plain, (![B_337]: (m1_subset_1(B_337, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_337, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_337, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4509, c_4499, c_4498, c_4509, c_4499, c_5129])).
% 7.14/2.40  tff(c_5287, plain, (![B_347]: (r1_tarski(B_347, k2_struct_0('#skF_2')) | ~m1_subset_1(B_347, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_347, '#skF_3'))), inference(resolution, [status(thm)], [c_5158, c_12])).
% 7.14/2.40  tff(c_5304, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_5287])).
% 7.14/2.40  tff(c_5313, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5106, c_5304])).
% 7.14/2.40  tff(c_5315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5157, c_5313])).
% 7.14/2.40  tff(c_5316, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5096])).
% 7.14/2.40  tff(c_5332, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5316, c_4509])).
% 7.14/2.40  tff(c_5333, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5316, c_4499])).
% 7.14/2.40  tff(c_5510, plain, (![C_352, A_353]: (m1_pre_topc(g1_pre_topc(u1_struct_0(C_352), u1_pre_topc(C_352)), A_353) | ~m1_pre_topc(C_352, A_353) | ~l1_pre_topc(C_352) | ~v2_pre_topc(C_352) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_352), u1_pre_topc(C_352))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_352), u1_pre_topc(C_352))) | ~l1_pre_topc(A_353))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.14/2.40  tff(c_5516, plain, (![A_353]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_353) | ~m1_pre_topc('#skF_2', A_353) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_353))), inference(superposition, [status(thm), theory('equality')], [c_5333, c_5510])).
% 7.14/2.40  tff(c_5530, plain, (![A_354]: (m1_pre_topc('#skF_3', A_354) | ~m1_pre_topc('#skF_2', A_354) | ~l1_pre_topc(A_354))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5332, c_5333, c_44, c_5332, c_5333, c_50, c_48, c_5332, c_5516])).
% 7.14/2.40  tff(c_5533, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4479, c_5530])).
% 7.14/2.40  tff(c_5536, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5533])).
% 7.14/2.40  tff(c_5538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4695, c_5536])).
% 7.14/2.40  tff(c_5540, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_4646])).
% 7.14/2.40  tff(c_4623, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4498, c_4614])).
% 7.14/2.40  tff(c_5617, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5540, c_4623])).
% 7.14/2.40  tff(c_4477, plain, (v1_borsuk_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 7.14/2.40  tff(c_5742, plain, (![B_366]: (v3_pre_topc(B_366, '#skF_3') | ~m1_subset_1(B_366, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_366, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4499, c_4509, c_4585])).
% 7.14/2.40  tff(c_5756, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_5742])).
% 7.14/2.40  tff(c_5757, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_5756])).
% 7.14/2.40  tff(c_5760, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_5757])).
% 7.14/2.40  tff(c_5764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_5760])).
% 7.14/2.40  tff(c_5766, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_5756])).
% 7.14/2.40  tff(c_5625, plain, (![B_359, A_360]: (m1_subset_1(B_359, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_360), u1_pre_topc(A_360))))) | ~m1_subset_1(B_359, k1_zfmisc_1(u1_struct_0(A_360))) | ~v3_pre_topc(B_359, A_360) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_5639, plain, (![B_359]: (m1_subset_1(B_359, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_359, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_359, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_5625])).
% 7.14/2.40  tff(c_6010, plain, (![B_379]: (m1_subset_1(B_379, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_379, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_379, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4499, c_4498, c_4509, c_5639])).
% 7.14/2.40  tff(c_6021, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_73, c_6010])).
% 7.14/2.40  tff(c_6026, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5766, c_6021])).
% 7.14/2.40  tff(c_6036, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6026, c_12])).
% 7.14/2.40  tff(c_6045, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6036, c_2])).
% 7.14/2.40  tff(c_6046, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_6045])).
% 7.14/2.40  tff(c_5767, plain, (![B_367, A_368]: (v3_pre_topc(B_367, A_368) | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_368), u1_pre_topc(A_368))))) | ~v3_pre_topc(B_367, g1_pre_topc(u1_struct_0(A_368), u1_pre_topc(A_368))) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_5777, plain, (![B_367]: (v3_pre_topc(B_367, '#skF_2') | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_367, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_5767])).
% 7.14/2.40  tff(c_5889, plain, (![B_373]: (v3_pre_topc(B_373, '#skF_2') | ~m1_subset_1(B_373, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_373, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4509, c_4499, c_4498, c_4509, c_5777])).
% 7.14/2.40  tff(c_5903, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_5889])).
% 7.14/2.40  tff(c_5904, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5903])).
% 7.14/2.40  tff(c_5907, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_5904])).
% 7.14/2.40  tff(c_5911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_5907])).
% 7.14/2.40  tff(c_5913, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_5903])).
% 7.14/2.40  tff(c_5914, plain, (![B_374, A_375]: (m1_subset_1(B_374, k1_zfmisc_1(u1_struct_0(A_375))) | ~m1_subset_1(B_374, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_375), u1_pre_topc(A_375))))) | ~v3_pre_topc(B_374, g1_pre_topc(u1_struct_0(A_375), u1_pre_topc(A_375))) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.14/2.40  tff(c_5936, plain, (![B_374]: (m1_subset_1(B_374, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_374, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_374, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_5914])).
% 7.14/2.40  tff(c_6070, plain, (![B_383]: (m1_subset_1(B_383, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_383, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_383, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4509, c_4499, c_4498, c_4509, c_4499, c_5936])).
% 7.14/2.40  tff(c_6104, plain, (![B_386]: (r1_tarski(B_386, k2_struct_0('#skF_2')) | ~m1_subset_1(B_386, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_386, '#skF_3'))), inference(resolution, [status(thm)], [c_6070, c_12])).
% 7.14/2.40  tff(c_6121, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_6104])).
% 7.14/2.40  tff(c_6130, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5913, c_6121])).
% 7.14/2.40  tff(c_6132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6046, c_6130])).
% 7.14/2.40  tff(c_6133, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_6045])).
% 7.14/2.40  tff(c_6150, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6133, c_4499])).
% 7.14/2.40  tff(c_5575, plain, (![B_357, A_358]: (v4_pre_topc(u1_struct_0(B_357), A_358) | ~v1_borsuk_1(B_357, A_358) | ~m1_subset_1(u1_struct_0(B_357), k1_zfmisc_1(u1_struct_0(A_358))) | ~m1_pre_topc(B_357, A_358) | ~l1_pre_topc(A_358) | ~v2_pre_topc(A_358))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.14/2.40  tff(c_5599, plain, (![B_357]: (v4_pre_topc(u1_struct_0(B_357), '#skF_1') | ~v1_borsuk_1(B_357, '#skF_1') | ~m1_subset_1(u1_struct_0(B_357), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_357, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4497, c_5575])).
% 7.14/2.40  tff(c_6843, plain, (![B_428]: (v4_pre_topc(u1_struct_0(B_428), '#skF_1') | ~v1_borsuk_1(B_428, '#skF_1') | ~m1_subset_1(u1_struct_0(B_428), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_428, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5599])).
% 7.14/2.40  tff(c_6846, plain, (v4_pre_topc(u1_struct_0('#skF_2'), '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6150, c_6843])).
% 7.14/2.40  tff(c_6860, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4479, c_5617, c_4477, c_6150, c_6846])).
% 7.14/2.40  tff(c_4654, plain, (![B_312, A_313]: (v1_borsuk_1(B_312, A_313) | ~v4_pre_topc(u1_struct_0(B_312), A_313) | ~m1_subset_1(u1_struct_0(B_312), k1_zfmisc_1(u1_struct_0(A_313))) | ~m1_pre_topc(B_312, A_313) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.14/2.40  tff(c_6676, plain, (![B_413, A_414]: (v1_borsuk_1(B_413, A_414) | ~v4_pre_topc(u1_struct_0(B_413), A_414) | ~v2_pre_topc(A_414) | ~m1_pre_topc(B_413, A_414) | ~l1_pre_topc(A_414))), inference(resolution, [status(thm)], [c_40, c_4654])).
% 7.14/2.40  tff(c_6685, plain, (![A_414]: (v1_borsuk_1('#skF_3', A_414) | ~v4_pre_topc(k2_struct_0('#skF_3'), A_414) | ~v2_pre_topc(A_414) | ~m1_pre_topc('#skF_3', A_414) | ~l1_pre_topc(A_414))), inference(superposition, [status(thm), theory('equality')], [c_4498, c_6676])).
% 7.14/2.40  tff(c_6872, plain, (v1_borsuk_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6860, c_6685])).
% 7.14/2.40  tff(c_6878, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5540, c_54, c_6872])).
% 7.14/2.40  tff(c_6880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4478, c_6878])).
% 7.14/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.14/2.40  
% 7.14/2.40  Inference rules
% 7.14/2.40  ----------------------
% 7.14/2.40  #Ref     : 0
% 7.14/2.40  #Sup     : 1397
% 7.14/2.40  #Fact    : 0
% 7.14/2.40  #Define  : 0
% 7.14/2.40  #Split   : 53
% 7.14/2.40  #Chain   : 0
% 7.14/2.40  #Close   : 0
% 7.14/2.40  
% 7.14/2.40  Ordering : KBO
% 7.14/2.40  
% 7.14/2.40  Simplification rules
% 7.14/2.40  ----------------------
% 7.14/2.40  #Subsume      : 418
% 7.14/2.40  #Demod        : 1748
% 7.14/2.40  #Tautology    : 365
% 7.14/2.40  #SimpNegUnit  : 25
% 7.14/2.40  #BackRed      : 61
% 7.14/2.40  
% 7.14/2.40  #Partial instantiations: 0
% 7.14/2.40  #Strategies tried      : 1
% 7.14/2.40  
% 7.14/2.40  Timing (in seconds)
% 7.14/2.40  ----------------------
% 7.14/2.41  Preprocessing        : 0.34
% 7.14/2.41  Parsing              : 0.18
% 7.14/2.41  CNF conversion       : 0.02
% 7.14/2.41  Main loop            : 1.25
% 7.14/2.41  Inferencing          : 0.42
% 7.14/2.41  Reduction            : 0.45
% 7.14/2.41  Demodulation         : 0.31
% 7.14/2.41  BG Simplification    : 0.04
% 7.14/2.41  Subsumption          : 0.23
% 7.14/2.41  Abstraction          : 0.05
% 7.14/2.41  MUC search           : 0.00
% 7.14/2.41  Cooper               : 0.00
% 7.14/2.41  Total                : 1.68
% 7.14/2.41  Index Insertion      : 0.00
% 7.14/2.41  Index Deletion       : 0.00
% 7.14/2.41  Index Matching       : 0.00
% 7.14/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
