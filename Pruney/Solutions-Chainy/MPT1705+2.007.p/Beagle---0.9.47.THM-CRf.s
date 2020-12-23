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
% DateTime   : Thu Dec  3 10:26:25 EST 2020

% Result     : Theorem 6.55s
% Output     : CNFRefutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :  242 (2472 expanded)
%              Number of leaves         :   31 ( 885 expanded)
%              Depth                    :   17
%              Number of atoms          :  584 (8076 expanded)
%              Number of equality atoms :   34 (1261 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_89,axiom,(
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

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_107,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_64,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_77,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    ! [A_10] :
      ( v3_pre_topc(k2_struct_0(A_10),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_14,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_101,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_89])).

tff(c_42,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2917,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42])).

tff(c_100,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_89])).

tff(c_3556,plain,(
    ! [B_246,A_247] :
      ( v3_pre_topc(B_246,A_247)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_247),u1_pre_topc(A_247)))))
      | ~ v3_pre_topc(B_246,g1_pre_topc(u1_struct_0(A_247),u1_pre_topc(A_247)))
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3582,plain,(
    ! [B_246] :
      ( v3_pre_topc(B_246,'#skF_2')
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_246,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_3556])).

tff(c_3602,plain,(
    ! [B_248] :
      ( v3_pre_topc(B_248,'#skF_2')
      | ~ m1_subset_1(B_248,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_248,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2917,c_101,c_100,c_2917,c_3582])).

tff(c_3636,plain,(
    ! [A_250] :
      ( v3_pre_topc(A_250,'#skF_2')
      | ~ v3_pre_topc(A_250,'#skF_3')
      | ~ r1_tarski(A_250,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_3602])).

tff(c_3651,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_3636])).

tff(c_3652,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3651])).

tff(c_3655,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_3652])).

tff(c_3659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3655])).

tff(c_3661,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3651])).

tff(c_3662,plain,(
    ! [B_251,A_252] :
      ( m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_252),u1_pre_topc(A_252)))))
      | ~ v3_pre_topc(B_251,g1_pre_topc(u1_struct_0(A_252),u1_pre_topc(A_252)))
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3688,plain,(
    ! [B_251] :
      ( m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_251,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_3662])).

tff(c_3749,plain,(
    ! [B_255] :
      ( m1_subset_1(B_255,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_255,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2917,c_101,c_100,c_2917,c_101,c_3688])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3762,plain,(
    ! [B_256] :
      ( r1_tarski(B_256,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_256,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3749,c_8])).

tff(c_3776,plain,(
    ! [A_257] :
      ( r1_tarski(A_257,k2_struct_0('#skF_2'))
      | ~ v3_pre_topc(A_257,'#skF_3')
      | ~ r1_tarski(A_257,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_3762])).

tff(c_3090,plain,(
    ! [B_216,A_217] :
      ( v3_pre_topc(B_216,g1_pre_topc(u1_struct_0(A_217),u1_pre_topc(A_217)))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ v3_pre_topc(B_216,A_217)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3093,plain,(
    ! [B_216] :
      ( v3_pre_topc(B_216,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_216,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_3090])).

tff(c_3230,plain,(
    ! [B_225] :
      ( v3_pre_topc(B_225,'#skF_3')
      | ~ m1_subset_1(B_225,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_225,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_101,c_2917,c_3093])).

tff(c_3240,plain,(
    ! [A_226] :
      ( v3_pre_topc(A_226,'#skF_3')
      | ~ v3_pre_topc(A_226,'#skF_2')
      | ~ r1_tarski(A_226,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_3230])).

tff(c_3249,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_3240])).

tff(c_3250,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3249])).

tff(c_3253,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3250])).

tff(c_3257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3253])).

tff(c_3259,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3249])).

tff(c_3397,plain,(
    ! [B_236,A_237] :
      ( m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_237),u1_pre_topc(A_237)))))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ v3_pre_topc(B_236,A_237)
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3411,plain,(
    ! [B_236] :
      ( m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_236,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_3397])).

tff(c_3526,plain,(
    ! [B_243] :
      ( m1_subset_1(B_243,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_243,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_101,c_100,c_2917,c_3411])).

tff(c_3536,plain,(
    ! [A_244] :
      ( m1_subset_1(A_244,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(A_244,'#skF_2')
      | ~ r1_tarski(A_244,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_3526])).

tff(c_3541,plain,(
    ! [A_245] :
      ( r1_tarski(A_245,k2_struct_0('#skF_3'))
      | ~ v3_pre_topc(A_245,'#skF_2')
      | ~ r1_tarski(A_245,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3536,c_8])).

tff(c_3548,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_3541])).

tff(c_3552,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3259,c_3548])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3555,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3552,c_2])).

tff(c_3601,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3555])).

tff(c_3782,plain,
    ( ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3776,c_3601])).

tff(c_3795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3661,c_3782])).

tff(c_3796,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3555])).

tff(c_3812,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3796,c_2917])).

tff(c_3813,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3796,c_101])).

tff(c_4029,plain,(
    ! [C_263,A_264] :
      ( m1_pre_topc(C_263,A_264)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_263),u1_pre_topc(C_263)),A_264)
      | ~ l1_pre_topc(C_263)
      | ~ v2_pre_topc(C_263)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_263),u1_pre_topc(C_263)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_263),u1_pre_topc(C_263)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4032,plain,(
    ! [A_264] :
      ( m1_pre_topc('#skF_2',A_264)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_264)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3813,c_4029])).

tff(c_4049,plain,(
    ! [A_265] :
      ( m1_pre_topc('#skF_2',A_265)
      | ~ m1_pre_topc('#skF_3',A_265)
      | ~ l1_pre_topc(A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3812,c_3813,c_44,c_3812,c_3813,c_50,c_48,c_3812,c_4032])).

tff(c_70,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_76,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_56,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_111,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_77,c_56])).

tff(c_112,plain,(
    ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_113,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42])).

tff(c_922,plain,(
    ! [C_97,A_98] :
      ( m1_pre_topc(C_97,A_98)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_97),u1_pre_topc(C_97)),A_98)
      | ~ l1_pre_topc(C_97)
      | ~ v2_pre_topc(C_97)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_97),u1_pre_topc(C_97)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_97),u1_pre_topc(C_97)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_928,plain,(
    ! [A_98] :
      ( m1_pre_topc('#skF_2',A_98)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_98)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_922])).

tff(c_942,plain,(
    ! [A_99] :
      ( m1_pre_topc('#skF_2',A_99)
      | ~ m1_pre_topc('#skF_3',A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_113,c_101,c_44,c_113,c_101,c_50,c_48,c_113,c_928])).

tff(c_99,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_142,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(u1_struct_0(B_48),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_pre_topc(B_48,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_163,plain,(
    ! [B_48] :
      ( m1_subset_1(u1_struct_0(B_48),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_48,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_142])).

tff(c_216,plain,(
    ! [B_55] :
      ( m1_subset_1(u1_struct_0(B_55),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_55,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_163])).

tff(c_240,plain,(
    ! [B_56] :
      ( r1_tarski(u1_struct_0(B_56),k2_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_56,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_216,c_8])).

tff(c_245,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_240])).

tff(c_256,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_960,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_942,c_256])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77,c_960])).

tff(c_986,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_225,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_216])).

tff(c_231,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_225])).

tff(c_1180,plain,(
    ! [B_111,A_112] :
      ( v3_pre_topc(u1_struct_0(B_111),A_112)
      | ~ v1_tsep_1(B_111,A_112)
      | ~ m1_subset_1(u1_struct_0(B_111),k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_pre_topc(B_111,A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1204,plain,(
    ! [B_111] :
      ( v3_pre_topc(u1_struct_0(B_111),'#skF_1')
      | ~ v1_tsep_1(B_111,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_111),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_111,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1180])).

tff(c_2880,plain,(
    ! [B_195] :
      ( v3_pre_topc(u1_struct_0(B_195),'#skF_1')
      | ~ v1_tsep_1(B_195,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_195),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_195,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1204])).

tff(c_2892,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2880])).

tff(c_2901,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_231,c_76,c_100,c_2892])).

tff(c_1436,plain,(
    ! [B_127,A_128] :
      ( v3_pre_topc(B_127,A_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128)))))
      | ~ v3_pre_topc(B_127,g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128)))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1462,plain,(
    ! [B_127] :
      ( v3_pre_topc(B_127,'#skF_2')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_127,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1436])).

tff(c_1481,plain,(
    ! [B_129] :
      ( v3_pre_topc(B_129,'#skF_2')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_129,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_113,c_101,c_100,c_113,c_1462])).

tff(c_1491,plain,(
    ! [A_130] :
      ( v3_pre_topc(A_130,'#skF_2')
      | ~ v3_pre_topc(A_130,'#skF_3')
      | ~ r1_tarski(A_130,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1481])).

tff(c_1500,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1491])).

tff(c_1501,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1500])).

tff(c_1523,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1501])).

tff(c_1527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1523])).

tff(c_1529,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1500])).

tff(c_1549,plain,(
    ! [B_133,A_134] :
      ( m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_134),u1_pre_topc(A_134)))))
      | ~ v3_pre_topc(B_133,g1_pre_topc(u1_struct_0(A_134),u1_pre_topc(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1575,plain,(
    ! [B_133] :
      ( m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_133,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1549])).

tff(c_1652,plain,(
    ! [B_138] :
      ( m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_138,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_113,c_101,c_100,c_113,c_101,c_1575])).

tff(c_1755,plain,(
    ! [B_144] :
      ( r1_tarski(B_144,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_144,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1652,c_8])).

tff(c_1769,plain,(
    ! [A_145] :
      ( r1_tarski(A_145,k2_struct_0('#skF_2'))
      | ~ v3_pre_topc(A_145,'#skF_3')
      | ~ r1_tarski(A_145,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1755])).

tff(c_1030,plain,(
    ! [B_102,A_103] :
      ( v3_pre_topc(B_102,g1_pre_topc(u1_struct_0(A_103),u1_pre_topc(A_103)))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ v3_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1033,plain,(
    ! [B_102] :
      ( v3_pre_topc(B_102,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_102,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1030])).

tff(c_1277,plain,(
    ! [B_116] :
      ( v3_pre_topc(B_116,'#skF_3')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_116,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_101,c_113,c_1033])).

tff(c_1287,plain,(
    ! [A_117] :
      ( v3_pre_topc(A_117,'#skF_3')
      | ~ v3_pre_topc(A_117,'#skF_2')
      | ~ r1_tarski(A_117,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1277])).

tff(c_1296,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_1287])).

tff(c_1297,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_1300,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1297])).

tff(c_1304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1300])).

tff(c_1306,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_1307,plain,(
    ! [B_118,A_119] :
      ( m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_119),u1_pre_topc(A_119)))))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ v3_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1321,plain,(
    ! [B_118] :
      ( m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_118,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1307])).

tff(c_1642,plain,(
    ! [B_137] :
      ( m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_137,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_101,c_100,c_113,c_1321])).

tff(c_1665,plain,(
    ! [A_139] :
      ( m1_subset_1(A_139,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(A_139,'#skF_2')
      | ~ r1_tarski(A_139,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1642])).

tff(c_1674,plain,(
    ! [A_140] :
      ( r1_tarski(A_140,k2_struct_0('#skF_3'))
      | ~ v3_pre_topc(A_140,'#skF_2')
      | ~ r1_tarski(A_140,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1665,c_8])).

tff(c_1681,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_1674])).

tff(c_1685,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1681])).

tff(c_1694,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1685,c_2])).

tff(c_1695,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1694])).

tff(c_1772,plain,
    ( ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1769,c_1695])).

tff(c_1787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1529,c_1772])).

tff(c_1788,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1694])).

tff(c_1829,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1788,c_101])).

tff(c_40,plain,(
    ! [B_30,A_28] :
      ( m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1056,plain,(
    ! [B_104,A_105] :
      ( v1_tsep_1(B_104,A_105)
      | ~ v3_pre_topc(u1_struct_0(B_104),A_105)
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2231,plain,(
    ! [B_162,A_163] :
      ( v1_tsep_1(B_162,A_163)
      | ~ v3_pre_topc(u1_struct_0(B_162),A_163)
      | ~ v2_pre_topc(A_163)
      | ~ m1_pre_topc(B_162,A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_40,c_1056])).

tff(c_2243,plain,(
    ! [A_163] :
      ( v1_tsep_1('#skF_2',A_163)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_163)
      | ~ v2_pre_topc(A_163)
      | ~ m1_pre_topc('#skF_2',A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1829,c_2231])).

tff(c_2905,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2901,c_2243])).

tff(c_2911,plain,(
    v1_tsep_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_986,c_54,c_2905])).

tff(c_2913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_2911])).

tff(c_2914,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_4069,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4049,c_2914])).

tff(c_4088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77,c_4069])).

tff(c_4090,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4089,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4095,plain,(
    ! [A_266] :
      ( u1_struct_0(A_266) = k2_struct_0(A_266)
      | ~ l1_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4102,plain,(
    ! [A_267] :
      ( u1_struct_0(A_267) = k2_struct_0(A_267)
      | ~ l1_pre_topc(A_267) ) ),
    inference(resolution,[status(thm)],[c_14,c_4095])).

tff(c_4114,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_4102])).

tff(c_4120,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4114,c_42])).

tff(c_4241,plain,(
    ! [B_283,A_284] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_283),u1_pre_topc(B_283)),A_284)
      | ~ m1_pre_topc(B_283,A_284)
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4249,plain,(
    ! [A_284] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_284)
      | ~ m1_pre_topc('#skF_2',A_284)
      | ~ l1_pre_topc(A_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4114,c_4241])).

tff(c_4255,plain,(
    ! [A_285] :
      ( m1_pre_topc('#skF_3',A_285)
      | ~ m1_pre_topc('#skF_2',A_285)
      | ~ l1_pre_topc(A_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4120,c_4249])).

tff(c_4258,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4089,c_4255])).

tff(c_4261,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4258])).

tff(c_4263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4090,c_4261])).

tff(c_4265,plain,(
    ~ v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4264,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4273,plain,(
    ! [A_286] :
      ( u1_struct_0(A_286) = k2_struct_0(A_286)
      | ~ l1_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4278,plain,(
    ! [A_287] :
      ( u1_struct_0(A_287) = k2_struct_0(A_287)
      | ~ l1_pre_topc(A_287) ) ),
    inference(resolution,[status(thm)],[c_14,c_4273])).

tff(c_4290,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_4278])).

tff(c_4296,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4290,c_42])).

tff(c_4417,plain,(
    ! [B_303,A_304] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_303),u1_pre_topc(B_303)),A_304)
      | ~ m1_pre_topc(B_303,A_304)
      | ~ l1_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4425,plain,(
    ! [A_304] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')),A_304)
      | ~ m1_pre_topc('#skF_2',A_304)
      | ~ l1_pre_topc(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4290,c_4417])).

tff(c_4431,plain,(
    ! [A_305] :
      ( m1_pre_topc('#skF_3',A_305)
      | ~ m1_pre_topc('#skF_2',A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4296,c_4425])).

tff(c_4434,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4264,c_4431])).

tff(c_4437,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4434])).

tff(c_4289,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_4278])).

tff(c_4288,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_4278])).

tff(c_4324,plain,(
    ! [B_295,A_296] :
      ( m1_subset_1(u1_struct_0(B_295),k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4345,plain,(
    ! [B_295] :
      ( m1_subset_1(u1_struct_0(B_295),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_295,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4288,c_4324])).

tff(c_4445,plain,(
    ! [B_306] :
      ( m1_subset_1(u1_struct_0(B_306),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_306,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4345])).

tff(c_4451,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4289,c_4445])).

tff(c_4460,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4437,c_4451])).

tff(c_72,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4271,plain,(
    v1_tsep_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_4265,c_72])).

tff(c_4837,plain,(
    ! [B_330,A_331] :
      ( v3_pre_topc(B_330,A_331)
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_331),u1_pre_topc(A_331)))))
      | ~ v3_pre_topc(B_330,g1_pre_topc(u1_struct_0(A_331),u1_pre_topc(A_331)))
      | ~ l1_pre_topc(A_331)
      | ~ v2_pre_topc(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4866,plain,(
    ! [B_330] :
      ( v3_pre_topc(B_330,'#skF_2')
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_330,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4290,c_4837])).

tff(c_4882,plain,(
    ! [B_332] :
      ( v3_pre_topc(B_332,'#skF_2')
      | ~ m1_subset_1(B_332,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_332,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4296,c_4290,c_4289,c_4296,c_4866])).

tff(c_4892,plain,(
    ! [A_333] :
      ( v3_pre_topc(A_333,'#skF_2')
      | ~ v3_pre_topc(A_333,'#skF_3')
      | ~ r1_tarski(A_333,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_4882])).

tff(c_4901,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_4892])).

tff(c_4902,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4901])).

tff(c_4934,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_4902])).

tff(c_4938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_4934])).

tff(c_4940,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_4901])).

tff(c_4960,plain,(
    ! [B_336,A_337] :
      ( m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_337),u1_pre_topc(A_337)))))
      | ~ v3_pre_topc(B_336,g1_pre_topc(u1_struct_0(A_337),u1_pre_topc(A_337)))
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4989,plain,(
    ! [B_336] :
      ( m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ v3_pre_topc(B_336,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4290,c_4960])).

tff(c_5110,plain,(
    ! [B_343] :
      ( m1_subset_1(B_343,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_343,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_343,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4296,c_4290,c_4289,c_4296,c_4290,c_4989])).

tff(c_5119,plain,(
    ! [B_344] :
      ( r1_tarski(B_344,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_344,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_344,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5110,c_8])).

tff(c_5128,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_struct_0('#skF_2'))
      | ~ v3_pre_topc(A_3,'#skF_3')
      | ~ r1_tarski(A_3,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_5119])).

tff(c_4467,plain,(
    ! [B_307,A_308] :
      ( v3_pre_topc(B_307,g1_pre_topc(u1_struct_0(A_308),u1_pre_topc(A_308)))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ v3_pre_topc(B_307,A_308)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4473,plain,(
    ! [B_307] :
      ( v3_pre_topc(B_307,g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_307,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4290,c_4467])).

tff(c_4695,plain,(
    ! [B_320] :
      ( v3_pre_topc(B_320,'#skF_3')
      | ~ m1_subset_1(B_320,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_320,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4290,c_4296,c_4473])).

tff(c_4705,plain,(
    ! [A_321] :
      ( v3_pre_topc(A_321,'#skF_3')
      | ~ v3_pre_topc(A_321,'#skF_2')
      | ~ r1_tarski(A_321,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_4695])).

tff(c_4714,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_4705])).

tff(c_4715,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4714])).

tff(c_4718,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_4715])).

tff(c_4722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4718])).

tff(c_4724,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4714])).

tff(c_4725,plain,(
    ! [B_322,A_323] :
      ( m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_323),u1_pre_topc(A_323)))))
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ v3_pre_topc(B_322,A_323)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4742,plain,(
    ! [B_322] :
      ( m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_322,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4290,c_4725])).

tff(c_5223,plain,(
    ! [B_350] :
      ( m1_subset_1(B_350,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_350,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_350,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4290,c_4289,c_4296,c_4742])).

tff(c_5237,plain,(
    ! [A_351] :
      ( m1_subset_1(A_351,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(A_351,'#skF_2')
      | ~ r1_tarski(A_351,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_5223])).

tff(c_5278,plain,(
    ! [A_353] :
      ( r1_tarski(A_353,k2_struct_0('#skF_3'))
      | ~ v3_pre_topc(A_353,'#skF_2')
      | ~ r1_tarski(A_353,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_5237,c_8])).

tff(c_5291,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_5278])).

tff(c_5297,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4724,c_5291])).

tff(c_5306,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5297,c_2])).

tff(c_5307,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5306])).

tff(c_5310,plain,
    ( ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5128,c_5307])).

tff(c_5314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4940,c_5310])).

tff(c_5315,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5306])).

tff(c_5340,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5315,c_4290])).

tff(c_4513,plain,(
    ! [B_310,A_311] :
      ( v3_pre_topc(u1_struct_0(B_310),A_311)
      | ~ v1_tsep_1(B_310,A_311)
      | ~ m1_subset_1(u1_struct_0(B_310),k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4537,plain,(
    ! [B_310] :
      ( v3_pre_topc(u1_struct_0(B_310),'#skF_1')
      | ~ v1_tsep_1(B_310,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_310),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_310,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4288,c_4513])).

tff(c_6384,plain,(
    ! [B_401] :
      ( v3_pre_topc(u1_struct_0(B_401),'#skF_1')
      | ~ v1_tsep_1(B_401,'#skF_1')
      | ~ m1_subset_1(u1_struct_0(B_401),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_401,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4537])).

tff(c_6387,plain,
    ( v3_pre_topc(u1_struct_0('#skF_2'),'#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5340,c_6384])).

tff(c_6401,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4264,c_4460,c_4271,c_5340,c_6387])).

tff(c_4552,plain,(
    ! [B_312,A_313] :
      ( v1_tsep_1(B_312,A_313)
      | ~ v3_pre_topc(u1_struct_0(B_312),A_313)
      | ~ m1_subset_1(u1_struct_0(B_312),k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ m1_pre_topc(B_312,A_313)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5543,plain,(
    ! [B_360,A_361] :
      ( v1_tsep_1(B_360,A_361)
      | ~ v3_pre_topc(u1_struct_0(B_360),A_361)
      | ~ v2_pre_topc(A_361)
      | ~ m1_pre_topc(B_360,A_361)
      | ~ l1_pre_topc(A_361) ) ),
    inference(resolution,[status(thm)],[c_40,c_4552])).

tff(c_5562,plain,(
    ! [A_361] :
      ( v1_tsep_1('#skF_3',A_361)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_361)
      | ~ v2_pre_topc(A_361)
      | ~ m1_pre_topc('#skF_3',A_361)
      | ~ l1_pre_topc(A_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4289,c_5543])).

tff(c_6457,plain,
    ( v1_tsep_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6401,c_5562])).

tff(c_6463,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4437,c_54,c_6457])).

tff(c_6465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4265,c_6463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.55/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.79/2.36  
% 6.79/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.79/2.36  %$ v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.79/2.36  
% 6.79/2.36  %Foreground sorts:
% 6.79/2.36  
% 6.79/2.36  
% 6.79/2.36  %Background operators:
% 6.79/2.36  
% 6.79/2.36  
% 6.79/2.36  %Foreground operators:
% 6.79/2.36  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.79/2.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.79/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.79/2.36  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.79/2.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.79/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.79/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.79/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.79/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.79/2.36  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.79/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.79/2.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.79/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.79/2.36  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.79/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.79/2.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.79/2.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.79/2.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.79/2.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.79/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.79/2.36  
% 6.79/2.39  tff(f_139, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tmap_1)).
% 6.79/2.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.79/2.39  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 6.79/2.39  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.79/2.39  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.79/2.39  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.79/2.39  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 6.79/2.39  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 6.79/2.39  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.79/2.39  tff(f_107, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 6.79/2.39  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 6.79/2.39  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_64, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_77, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 6.79/2.39  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.79/2.39  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_24, plain, (![A_10]: (v3_pre_topc(k2_struct_0(A_10), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.79/2.39  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.79/2.39  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_14, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.79/2.39  tff(c_83, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.79/2.39  tff(c_89, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_14, c_83])).
% 6.79/2.39  tff(c_101, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_89])).
% 6.79/2.39  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_2917, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_42])).
% 6.79/2.39  tff(c_100, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_89])).
% 6.79/2.39  tff(c_3556, plain, (![B_246, A_247]: (v3_pre_topc(B_246, A_247) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_247), u1_pre_topc(A_247))))) | ~v3_pre_topc(B_246, g1_pre_topc(u1_struct_0(A_247), u1_pre_topc(A_247))) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.39  tff(c_3582, plain, (![B_246]: (v3_pre_topc(B_246, '#skF_2') | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_246, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_3556])).
% 6.79/2.39  tff(c_3602, plain, (![B_248]: (v3_pre_topc(B_248, '#skF_2') | ~m1_subset_1(B_248, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_248, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2917, c_101, c_100, c_2917, c_3582])).
% 6.79/2.39  tff(c_3636, plain, (![A_250]: (v3_pre_topc(A_250, '#skF_2') | ~v3_pre_topc(A_250, '#skF_3') | ~r1_tarski(A_250, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_3602])).
% 6.79/2.39  tff(c_3651, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_3636])).
% 6.79/2.39  tff(c_3652, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3651])).
% 6.79/2.39  tff(c_3655, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_3652])).
% 6.79/2.39  tff(c_3659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3655])).
% 6.79/2.39  tff(c_3661, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_3651])).
% 6.79/2.39  tff(c_3662, plain, (![B_251, A_252]: (m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_252))) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_252), u1_pre_topc(A_252))))) | ~v3_pre_topc(B_251, g1_pre_topc(u1_struct_0(A_252), u1_pre_topc(A_252))) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.39  tff(c_3688, plain, (![B_251]: (m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_251, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_3662])).
% 6.79/2.39  tff(c_3749, plain, (![B_255]: (m1_subset_1(B_255, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_255, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_255, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2917, c_101, c_100, c_2917, c_101, c_3688])).
% 6.79/2.39  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.79/2.39  tff(c_3762, plain, (![B_256]: (r1_tarski(B_256, k2_struct_0('#skF_2')) | ~m1_subset_1(B_256, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_256, '#skF_3'))), inference(resolution, [status(thm)], [c_3749, c_8])).
% 6.79/2.39  tff(c_3776, plain, (![A_257]: (r1_tarski(A_257, k2_struct_0('#skF_2')) | ~v3_pre_topc(A_257, '#skF_3') | ~r1_tarski(A_257, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_3762])).
% 6.79/2.39  tff(c_3090, plain, (![B_216, A_217]: (v3_pre_topc(B_216, g1_pre_topc(u1_struct_0(A_217), u1_pre_topc(A_217))) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_217))) | ~v3_pre_topc(B_216, A_217) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.39  tff(c_3093, plain, (![B_216]: (v3_pre_topc(B_216, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_216, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_3090])).
% 6.79/2.39  tff(c_3230, plain, (![B_225]: (v3_pre_topc(B_225, '#skF_3') | ~m1_subset_1(B_225, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_225, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_101, c_2917, c_3093])).
% 6.79/2.39  tff(c_3240, plain, (![A_226]: (v3_pre_topc(A_226, '#skF_3') | ~v3_pre_topc(A_226, '#skF_2') | ~r1_tarski(A_226, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_3230])).
% 6.79/2.39  tff(c_3249, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_3240])).
% 6.79/2.39  tff(c_3250, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3249])).
% 6.79/2.39  tff(c_3253, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3250])).
% 6.79/2.39  tff(c_3257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3253])).
% 6.79/2.39  tff(c_3259, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_3249])).
% 6.79/2.39  tff(c_3397, plain, (![B_236, A_237]: (m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_237), u1_pre_topc(A_237))))) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(A_237))) | ~v3_pre_topc(B_236, A_237) | ~l1_pre_topc(A_237) | ~v2_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.39  tff(c_3411, plain, (![B_236]: (m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_236, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_3397])).
% 6.79/2.39  tff(c_3526, plain, (![B_243]: (m1_subset_1(B_243, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_243, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_243, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_101, c_100, c_2917, c_3411])).
% 6.79/2.39  tff(c_3536, plain, (![A_244]: (m1_subset_1(A_244, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(A_244, '#skF_2') | ~r1_tarski(A_244, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_3526])).
% 6.79/2.39  tff(c_3541, plain, (![A_245]: (r1_tarski(A_245, k2_struct_0('#skF_3')) | ~v3_pre_topc(A_245, '#skF_2') | ~r1_tarski(A_245, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3536, c_8])).
% 6.79/2.39  tff(c_3548, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_3541])).
% 6.79/2.39  tff(c_3552, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3259, c_3548])).
% 6.79/2.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.79/2.39  tff(c_3555, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3552, c_2])).
% 6.79/2.39  tff(c_3601, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_3555])).
% 6.79/2.39  tff(c_3782, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3776, c_3601])).
% 6.79/2.39  tff(c_3795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3661, c_3782])).
% 6.79/2.39  tff(c_3796, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_3555])).
% 6.79/2.39  tff(c_3812, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3796, c_2917])).
% 6.79/2.39  tff(c_3813, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3796, c_101])).
% 6.79/2.39  tff(c_4029, plain, (![C_263, A_264]: (m1_pre_topc(C_263, A_264) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_263), u1_pre_topc(C_263)), A_264) | ~l1_pre_topc(C_263) | ~v2_pre_topc(C_263) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_263), u1_pre_topc(C_263))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_263), u1_pre_topc(C_263))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.79/2.39  tff(c_4032, plain, (![A_264]: (m1_pre_topc('#skF_2', A_264) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_264) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_264))), inference(superposition, [status(thm), theory('equality')], [c_3813, c_4029])).
% 6.79/2.39  tff(c_4049, plain, (![A_265]: (m1_pre_topc('#skF_2', A_265) | ~m1_pre_topc('#skF_3', A_265) | ~l1_pre_topc(A_265))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3812, c_3813, c_44, c_3812, c_3813, c_50, c_48, c_3812, c_4032])).
% 6.79/2.39  tff(c_70, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_76, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 6.79/2.39  tff(c_56, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.39  tff(c_111, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_77, c_56])).
% 6.79/2.39  tff(c_112, plain, (~v1_tsep_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_111])).
% 6.79/2.39  tff(c_113, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_42])).
% 6.79/2.39  tff(c_922, plain, (![C_97, A_98]: (m1_pre_topc(C_97, A_98) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_97), u1_pre_topc(C_97)), A_98) | ~l1_pre_topc(C_97) | ~v2_pre_topc(C_97) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_97), u1_pre_topc(C_97))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_97), u1_pre_topc(C_97))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.79/2.39  tff(c_928, plain, (![A_98]: (m1_pre_topc('#skF_2', A_98) | ~m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_98) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_98))), inference(superposition, [status(thm), theory('equality')], [c_101, c_922])).
% 6.79/2.40  tff(c_942, plain, (![A_99]: (m1_pre_topc('#skF_2', A_99) | ~m1_pre_topc('#skF_3', A_99) | ~l1_pre_topc(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_113, c_101, c_44, c_113, c_101, c_50, c_48, c_113, c_928])).
% 6.79/2.40  tff(c_99, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_89])).
% 6.79/2.40  tff(c_142, plain, (![B_48, A_49]: (m1_subset_1(u1_struct_0(B_48), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_pre_topc(B_48, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.79/2.40  tff(c_163, plain, (![B_48]: (m1_subset_1(u1_struct_0(B_48), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_48, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_142])).
% 6.79/2.40  tff(c_216, plain, (![B_55]: (m1_subset_1(u1_struct_0(B_55), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_55, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_163])).
% 6.79/2.40  tff(c_240, plain, (![B_56]: (r1_tarski(u1_struct_0(B_56), k2_struct_0('#skF_1')) | ~m1_pre_topc(B_56, '#skF_1'))), inference(resolution, [status(thm)], [c_216, c_8])).
% 6.79/2.40  tff(c_245, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_240])).
% 6.79/2.40  tff(c_256, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_245])).
% 6.79/2.40  tff(c_960, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_942, c_256])).
% 6.79/2.40  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_77, c_960])).
% 6.79/2.40  tff(c_986, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_245])).
% 6.79/2.40  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.40  tff(c_225, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100, c_216])).
% 6.79/2.40  tff(c_231, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_225])).
% 6.79/2.40  tff(c_1180, plain, (![B_111, A_112]: (v3_pre_topc(u1_struct_0(B_111), A_112) | ~v1_tsep_1(B_111, A_112) | ~m1_subset_1(u1_struct_0(B_111), k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_pre_topc(B_111, A_112) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.79/2.40  tff(c_1204, plain, (![B_111]: (v3_pre_topc(u1_struct_0(B_111), '#skF_1') | ~v1_tsep_1(B_111, '#skF_1') | ~m1_subset_1(u1_struct_0(B_111), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_111, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1180])).
% 6.79/2.40  tff(c_2880, plain, (![B_195]: (v3_pre_topc(u1_struct_0(B_195), '#skF_1') | ~v1_tsep_1(B_195, '#skF_1') | ~m1_subset_1(u1_struct_0(B_195), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_195, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1204])).
% 6.79/2.40  tff(c_2892, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100, c_2880])).
% 6.79/2.40  tff(c_2901, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_231, c_76, c_100, c_2892])).
% 6.79/2.40  tff(c_1436, plain, (![B_127, A_128]: (v3_pre_topc(B_127, A_128) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_128), u1_pre_topc(A_128))))) | ~v3_pre_topc(B_127, g1_pre_topc(u1_struct_0(A_128), u1_pre_topc(A_128))) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.40  tff(c_1462, plain, (![B_127]: (v3_pre_topc(B_127, '#skF_2') | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_127, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1436])).
% 6.79/2.40  tff(c_1481, plain, (![B_129]: (v3_pre_topc(B_129, '#skF_2') | ~m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_129, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_113, c_101, c_100, c_113, c_1462])).
% 6.79/2.40  tff(c_1491, plain, (![A_130]: (v3_pre_topc(A_130, '#skF_2') | ~v3_pre_topc(A_130, '#skF_3') | ~r1_tarski(A_130, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_1481])).
% 6.79/2.40  tff(c_1500, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_1491])).
% 6.79/2.40  tff(c_1501, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1500])).
% 6.79/2.40  tff(c_1523, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1501])).
% 6.79/2.40  tff(c_1527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1523])).
% 6.79/2.40  tff(c_1529, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1500])).
% 6.79/2.40  tff(c_1549, plain, (![B_133, A_134]: (m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_134), u1_pre_topc(A_134))))) | ~v3_pre_topc(B_133, g1_pre_topc(u1_struct_0(A_134), u1_pre_topc(A_134))) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.40  tff(c_1575, plain, (![B_133]: (m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_133, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1549])).
% 6.79/2.40  tff(c_1652, plain, (![B_138]: (m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_138, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_113, c_101, c_100, c_113, c_101, c_1575])).
% 6.79/2.40  tff(c_1755, plain, (![B_144]: (r1_tarski(B_144, k2_struct_0('#skF_2')) | ~m1_subset_1(B_144, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_144, '#skF_3'))), inference(resolution, [status(thm)], [c_1652, c_8])).
% 6.79/2.40  tff(c_1769, plain, (![A_145]: (r1_tarski(A_145, k2_struct_0('#skF_2')) | ~v3_pre_topc(A_145, '#skF_3') | ~r1_tarski(A_145, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_1755])).
% 6.79/2.40  tff(c_1030, plain, (![B_102, A_103]: (v3_pre_topc(B_102, g1_pre_topc(u1_struct_0(A_103), u1_pre_topc(A_103))) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~v3_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.40  tff(c_1033, plain, (![B_102]: (v3_pre_topc(B_102, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_102, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1030])).
% 6.79/2.40  tff(c_1277, plain, (![B_116]: (v3_pre_topc(B_116, '#skF_3') | ~m1_subset_1(B_116, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_116, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_101, c_113, c_1033])).
% 6.79/2.40  tff(c_1287, plain, (![A_117]: (v3_pre_topc(A_117, '#skF_3') | ~v3_pre_topc(A_117, '#skF_2') | ~r1_tarski(A_117, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_1277])).
% 6.79/2.40  tff(c_1296, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_1287])).
% 6.79/2.40  tff(c_1297, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1296])).
% 6.79/2.40  tff(c_1300, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1297])).
% 6.79/2.40  tff(c_1304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1300])).
% 6.79/2.40  tff(c_1306, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_1296])).
% 6.79/2.40  tff(c_1307, plain, (![B_118, A_119]: (m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_119), u1_pre_topc(A_119))))) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~v3_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.40  tff(c_1321, plain, (![B_118]: (m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_118, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1307])).
% 6.79/2.40  tff(c_1642, plain, (![B_137]: (m1_subset_1(B_137, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_137, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_137, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_101, c_100, c_113, c_1321])).
% 6.79/2.40  tff(c_1665, plain, (![A_139]: (m1_subset_1(A_139, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(A_139, '#skF_2') | ~r1_tarski(A_139, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_1642])).
% 6.79/2.40  tff(c_1674, plain, (![A_140]: (r1_tarski(A_140, k2_struct_0('#skF_3')) | ~v3_pre_topc(A_140, '#skF_2') | ~r1_tarski(A_140, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1665, c_8])).
% 6.79/2.40  tff(c_1681, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_1674])).
% 6.79/2.40  tff(c_1685, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1681])).
% 6.79/2.40  tff(c_1694, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1685, c_2])).
% 6.79/2.40  tff(c_1695, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1694])).
% 6.79/2.40  tff(c_1772, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1769, c_1695])).
% 6.79/2.40  tff(c_1787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1529, c_1772])).
% 6.79/2.40  tff(c_1788, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1694])).
% 6.79/2.40  tff(c_1829, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1788, c_101])).
% 6.79/2.40  tff(c_40, plain, (![B_30, A_28]: (m1_subset_1(u1_struct_0(B_30), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.79/2.40  tff(c_1056, plain, (![B_104, A_105]: (v1_tsep_1(B_104, A_105) | ~v3_pre_topc(u1_struct_0(B_104), A_105) | ~m1_subset_1(u1_struct_0(B_104), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.79/2.40  tff(c_2231, plain, (![B_162, A_163]: (v1_tsep_1(B_162, A_163) | ~v3_pre_topc(u1_struct_0(B_162), A_163) | ~v2_pre_topc(A_163) | ~m1_pre_topc(B_162, A_163) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_40, c_1056])).
% 6.79/2.40  tff(c_2243, plain, (![A_163]: (v1_tsep_1('#skF_2', A_163) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_163) | ~v2_pre_topc(A_163) | ~m1_pre_topc('#skF_2', A_163) | ~l1_pre_topc(A_163))), inference(superposition, [status(thm), theory('equality')], [c_1829, c_2231])).
% 6.79/2.40  tff(c_2905, plain, (v1_tsep_1('#skF_2', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2901, c_2243])).
% 6.79/2.40  tff(c_2911, plain, (v1_tsep_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_986, c_54, c_2905])).
% 6.79/2.40  tff(c_2913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_2911])).
% 6.79/2.40  tff(c_2914, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_111])).
% 6.79/2.40  tff(c_4069, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4049, c_2914])).
% 6.79/2.40  tff(c_4088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_77, c_4069])).
% 6.79/2.40  tff(c_4090, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 6.79/2.40  tff(c_4089, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 6.79/2.40  tff(c_4095, plain, (![A_266]: (u1_struct_0(A_266)=k2_struct_0(A_266) | ~l1_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.79/2.40  tff(c_4102, plain, (![A_267]: (u1_struct_0(A_267)=k2_struct_0(A_267) | ~l1_pre_topc(A_267))), inference(resolution, [status(thm)], [c_14, c_4095])).
% 6.79/2.40  tff(c_4114, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_4102])).
% 6.79/2.40  tff(c_4120, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4114, c_42])).
% 6.79/2.40  tff(c_4241, plain, (![B_283, A_284]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_283), u1_pre_topc(B_283)), A_284) | ~m1_pre_topc(B_283, A_284) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.79/2.40  tff(c_4249, plain, (![A_284]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_284) | ~m1_pre_topc('#skF_2', A_284) | ~l1_pre_topc(A_284))), inference(superposition, [status(thm), theory('equality')], [c_4114, c_4241])).
% 6.79/2.40  tff(c_4255, plain, (![A_285]: (m1_pre_topc('#skF_3', A_285) | ~m1_pre_topc('#skF_2', A_285) | ~l1_pre_topc(A_285))), inference(demodulation, [status(thm), theory('equality')], [c_4120, c_4249])).
% 6.79/2.40  tff(c_4258, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4089, c_4255])).
% 6.79/2.40  tff(c_4261, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4258])).
% 6.79/2.40  tff(c_4263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4090, c_4261])).
% 6.79/2.40  tff(c_4265, plain, (~v1_tsep_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 6.79/2.40  tff(c_4264, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 6.79/2.40  tff(c_4273, plain, (![A_286]: (u1_struct_0(A_286)=k2_struct_0(A_286) | ~l1_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.79/2.40  tff(c_4278, plain, (![A_287]: (u1_struct_0(A_287)=k2_struct_0(A_287) | ~l1_pre_topc(A_287))), inference(resolution, [status(thm)], [c_14, c_4273])).
% 6.79/2.40  tff(c_4290, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_4278])).
% 6.79/2.40  tff(c_4296, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4290, c_42])).
% 6.79/2.40  tff(c_4417, plain, (![B_303, A_304]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_303), u1_pre_topc(B_303)), A_304) | ~m1_pre_topc(B_303, A_304) | ~l1_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.79/2.40  tff(c_4425, plain, (![A_304]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')), A_304) | ~m1_pre_topc('#skF_2', A_304) | ~l1_pre_topc(A_304))), inference(superposition, [status(thm), theory('equality')], [c_4290, c_4417])).
% 6.79/2.40  tff(c_4431, plain, (![A_305]: (m1_pre_topc('#skF_3', A_305) | ~m1_pre_topc('#skF_2', A_305) | ~l1_pre_topc(A_305))), inference(demodulation, [status(thm), theory('equality')], [c_4296, c_4425])).
% 6.79/2.40  tff(c_4434, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4264, c_4431])).
% 6.79/2.40  tff(c_4437, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4434])).
% 6.79/2.40  tff(c_4289, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_4278])).
% 6.79/2.40  tff(c_4288, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_4278])).
% 6.79/2.40  tff(c_4324, plain, (![B_295, A_296]: (m1_subset_1(u1_struct_0(B_295), k1_zfmisc_1(u1_struct_0(A_296))) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.79/2.40  tff(c_4345, plain, (![B_295]: (m1_subset_1(u1_struct_0(B_295), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_295, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4288, c_4324])).
% 6.79/2.40  tff(c_4445, plain, (![B_306]: (m1_subset_1(u1_struct_0(B_306), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_306, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4345])).
% 6.79/2.40  tff(c_4451, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4289, c_4445])).
% 6.79/2.40  tff(c_4460, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4437, c_4451])).
% 6.79/2.40  tff(c_72, plain, (v1_tsep_1('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.79/2.40  tff(c_4271, plain, (v1_tsep_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_4265, c_72])).
% 6.79/2.40  tff(c_4837, plain, (![B_330, A_331]: (v3_pre_topc(B_330, A_331) | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_331), u1_pre_topc(A_331))))) | ~v3_pre_topc(B_330, g1_pre_topc(u1_struct_0(A_331), u1_pre_topc(A_331))) | ~l1_pre_topc(A_331) | ~v2_pre_topc(A_331))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.40  tff(c_4866, plain, (![B_330]: (v3_pre_topc(B_330, '#skF_2') | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_330, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4290, c_4837])).
% 6.79/2.40  tff(c_4882, plain, (![B_332]: (v3_pre_topc(B_332, '#skF_2') | ~m1_subset_1(B_332, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_332, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4296, c_4290, c_4289, c_4296, c_4866])).
% 6.79/2.40  tff(c_4892, plain, (![A_333]: (v3_pre_topc(A_333, '#skF_2') | ~v3_pre_topc(A_333, '#skF_3') | ~r1_tarski(A_333, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_4882])).
% 6.79/2.40  tff(c_4901, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_4892])).
% 6.79/2.40  tff(c_4902, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_4901])).
% 6.79/2.40  tff(c_4934, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_4902])).
% 6.79/2.40  tff(c_4938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_4934])).
% 6.79/2.40  tff(c_4940, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_4901])).
% 6.79/2.40  tff(c_4960, plain, (![B_336, A_337]: (m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0(A_337))) | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_337), u1_pre_topc(A_337))))) | ~v3_pre_topc(B_336, g1_pre_topc(u1_struct_0(A_337), u1_pre_topc(A_337))) | ~l1_pre_topc(A_337) | ~v2_pre_topc(A_337))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.40  tff(c_4989, plain, (![B_336]: (m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v3_pre_topc(B_336, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4290, c_4960])).
% 6.79/2.40  tff(c_5110, plain, (![B_343]: (m1_subset_1(B_343, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_343, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_343, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4296, c_4290, c_4289, c_4296, c_4290, c_4989])).
% 6.79/2.40  tff(c_5119, plain, (![B_344]: (r1_tarski(B_344, k2_struct_0('#skF_2')) | ~m1_subset_1(B_344, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_344, '#skF_3'))), inference(resolution, [status(thm)], [c_5110, c_8])).
% 6.79/2.40  tff(c_5128, plain, (![A_3]: (r1_tarski(A_3, k2_struct_0('#skF_2')) | ~v3_pre_topc(A_3, '#skF_3') | ~r1_tarski(A_3, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_5119])).
% 6.79/2.40  tff(c_4467, plain, (![B_307, A_308]: (v3_pre_topc(B_307, g1_pre_topc(u1_struct_0(A_308), u1_pre_topc(A_308))) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_308))) | ~v3_pre_topc(B_307, A_308) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.40  tff(c_4473, plain, (![B_307]: (v3_pre_topc(B_307, g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_307, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4290, c_4467])).
% 6.79/2.40  tff(c_4695, plain, (![B_320]: (v3_pre_topc(B_320, '#skF_3') | ~m1_subset_1(B_320, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_320, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4290, c_4296, c_4473])).
% 6.79/2.40  tff(c_4705, plain, (![A_321]: (v3_pre_topc(A_321, '#skF_3') | ~v3_pre_topc(A_321, '#skF_2') | ~r1_tarski(A_321, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_4695])).
% 6.79/2.40  tff(c_4714, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_4705])).
% 6.79/2.40  tff(c_4715, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_4714])).
% 6.79/2.40  tff(c_4718, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_4715])).
% 6.79/2.40  tff(c_4722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4718])).
% 6.79/2.40  tff(c_4724, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_4714])).
% 6.79/2.40  tff(c_4725, plain, (![B_322, A_323]: (m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_323), u1_pre_topc(A_323))))) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(A_323))) | ~v3_pre_topc(B_322, A_323) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.79/2.40  tff(c_4742, plain, (![B_322]: (m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_322, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4290, c_4725])).
% 6.79/2.40  tff(c_5223, plain, (![B_350]: (m1_subset_1(B_350, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_350, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_350, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4290, c_4289, c_4296, c_4742])).
% 6.79/2.40  tff(c_5237, plain, (![A_351]: (m1_subset_1(A_351, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(A_351, '#skF_2') | ~r1_tarski(A_351, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_5223])).
% 6.79/2.40  tff(c_5278, plain, (![A_353]: (r1_tarski(A_353, k2_struct_0('#skF_3')) | ~v3_pre_topc(A_353, '#skF_2') | ~r1_tarski(A_353, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_5237, c_8])).
% 6.79/2.40  tff(c_5291, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_5278])).
% 6.79/2.40  tff(c_5297, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4724, c_5291])).
% 6.79/2.40  tff(c_5306, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_5297, c_2])).
% 6.79/2.40  tff(c_5307, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_5306])).
% 6.79/2.40  tff(c_5310, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_5128, c_5307])).
% 6.79/2.40  tff(c_5314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4940, c_5310])).
% 6.79/2.40  tff(c_5315, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5306])).
% 6.79/2.40  tff(c_5340, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5315, c_4290])).
% 6.79/2.40  tff(c_4513, plain, (![B_310, A_311]: (v3_pre_topc(u1_struct_0(B_310), A_311) | ~v1_tsep_1(B_310, A_311) | ~m1_subset_1(u1_struct_0(B_310), k1_zfmisc_1(u1_struct_0(A_311))) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.79/2.40  tff(c_4537, plain, (![B_310]: (v3_pre_topc(u1_struct_0(B_310), '#skF_1') | ~v1_tsep_1(B_310, '#skF_1') | ~m1_subset_1(u1_struct_0(B_310), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_310, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4288, c_4513])).
% 6.79/2.40  tff(c_6384, plain, (![B_401]: (v3_pre_topc(u1_struct_0(B_401), '#skF_1') | ~v1_tsep_1(B_401, '#skF_1') | ~m1_subset_1(u1_struct_0(B_401), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc(B_401, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4537])).
% 6.79/2.40  tff(c_6387, plain, (v3_pre_topc(u1_struct_0('#skF_2'), '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5340, c_6384])).
% 6.79/2.40  tff(c_6401, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4264, c_4460, c_4271, c_5340, c_6387])).
% 6.79/2.40  tff(c_4552, plain, (![B_312, A_313]: (v1_tsep_1(B_312, A_313) | ~v3_pre_topc(u1_struct_0(B_312), A_313) | ~m1_subset_1(u1_struct_0(B_312), k1_zfmisc_1(u1_struct_0(A_313))) | ~m1_pre_topc(B_312, A_313) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.79/2.40  tff(c_5543, plain, (![B_360, A_361]: (v1_tsep_1(B_360, A_361) | ~v3_pre_topc(u1_struct_0(B_360), A_361) | ~v2_pre_topc(A_361) | ~m1_pre_topc(B_360, A_361) | ~l1_pre_topc(A_361))), inference(resolution, [status(thm)], [c_40, c_4552])).
% 6.79/2.40  tff(c_5562, plain, (![A_361]: (v1_tsep_1('#skF_3', A_361) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_361) | ~v2_pre_topc(A_361) | ~m1_pre_topc('#skF_3', A_361) | ~l1_pre_topc(A_361))), inference(superposition, [status(thm), theory('equality')], [c_4289, c_5543])).
% 6.79/2.40  tff(c_6457, plain, (v1_tsep_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6401, c_5562])).
% 6.79/2.40  tff(c_6463, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4437, c_54, c_6457])).
% 6.79/2.40  tff(c_6465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4265, c_6463])).
% 6.79/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.79/2.40  
% 6.79/2.40  Inference rules
% 6.79/2.40  ----------------------
% 6.79/2.40  #Ref     : 0
% 6.79/2.40  #Sup     : 1328
% 6.79/2.40  #Fact    : 0
% 6.79/2.40  #Define  : 0
% 6.79/2.40  #Split   : 48
% 6.79/2.40  #Chain   : 0
% 6.79/2.40  #Close   : 0
% 6.79/2.40  
% 6.79/2.40  Ordering : KBO
% 6.79/2.40  
% 6.79/2.40  Simplification rules
% 6.79/2.40  ----------------------
% 6.79/2.40  #Subsume      : 551
% 6.79/2.40  #Demod        : 1517
% 6.79/2.40  #Tautology    : 216
% 6.79/2.40  #SimpNegUnit  : 19
% 6.79/2.40  #BackRed      : 55
% 6.79/2.40  
% 6.79/2.40  #Partial instantiations: 0
% 6.79/2.40  #Strategies tried      : 1
% 6.79/2.40  
% 6.79/2.40  Timing (in seconds)
% 6.79/2.40  ----------------------
% 7.01/2.40  Preprocessing        : 0.36
% 7.01/2.40  Parsing              : 0.19
% 7.01/2.40  CNF conversion       : 0.02
% 7.01/2.40  Main loop            : 1.20
% 7.01/2.40  Inferencing          : 0.41
% 7.01/2.40  Reduction            : 0.42
% 7.01/2.40  Demodulation         : 0.29
% 7.01/2.40  BG Simplification    : 0.04
% 7.01/2.40  Subsumption          : 0.24
% 7.01/2.40  Abstraction          : 0.05
% 7.01/2.40  MUC search           : 0.00
% 7.01/2.40  Cooper               : 0.00
% 7.01/2.40  Total                : 1.64
% 7.01/2.40  Index Insertion      : 0.00
% 7.01/2.40  Index Deletion       : 0.00
% 7.01/2.40  Index Matching       : 0.00
% 7.01/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
