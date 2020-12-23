%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:24 EST 2020

% Result     : Theorem 11.17s
% Output     : CNFRefutation 11.23s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 951 expanded)
%              Number of leaves         :   35 ( 333 expanded)
%              Depth                    :   15
%              Number of atoms          :  532 (3796 expanded)
%              Number of equality atoms :   43 ( 194 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_58,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_12346,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_67,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_78,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_68,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_36,plain,(
    ! [A_25,B_27] :
      ( v5_tops_1(k3_subset_1(u1_struct_0(A_25),B_27),A_25)
      | ~ v6_tops_1(B_27,A_25)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_210,plain,(
    ! [A_72,B_73] :
      ( k2_pre_topc(A_72,k1_tops_1(A_72,B_73)) = B_73
      | ~ v5_tops_1(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1760,plain,(
    ! [A_136,B_137] :
      ( k2_pre_topc(A_136,k1_tops_1(A_136,k3_subset_1(u1_struct_0(A_136),B_137))) = k3_subset_1(u1_struct_0(A_136),B_137)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_136),B_137),A_136)
      | ~ l1_pre_topc(A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136))) ) ),
    inference(resolution,[status(thm)],[c_8,c_210])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k1_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_107,plain,(
    ! [A_58,B_59] :
      ( v4_pre_topc(k2_pre_topc(A_58,B_59),A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_117,plain,(
    ! [A_19,B_20] :
      ( v4_pre_topc(k2_pre_topc(A_19,k1_tops_1(A_19,B_20)),A_19)
      | ~ v2_pre_topc(A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_5404,plain,(
    ! [A_196,B_197] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_196),B_197),A_196)
      | ~ v2_pre_topc(A_196)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_196),B_197),k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_196),B_197),A_196)
      | ~ l1_pre_topc(A_196)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_117])).

tff(c_5410,plain,(
    ! [A_198,B_199] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_198),B_199),A_198)
      | ~ v2_pre_topc(A_198)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_198),B_199),A_198)
      | ~ l1_pre_topc(A_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198))) ) ),
    inference(resolution,[status(thm)],[c_8,c_5404])).

tff(c_5415,plain,(
    ! [A_200,B_201] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_200),B_201),A_200)
      | ~ v2_pre_topc(A_200)
      | ~ v6_tops_1(B_201,A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(resolution,[status(thm)],[c_36,c_5410])).

tff(c_38,plain,(
    ! [B_30,A_28] :
      ( v3_pre_topc(B_30,A_28)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_28),B_30),A_28)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5546,plain,(
    ! [B_204,A_205] :
      ( v3_pre_topc(B_204,A_205)
      | ~ v2_pre_topc(A_205)
      | ~ v6_tops_1(B_204,A_205)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_5415,c_38])).

tff(c_5583,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_5546])).

tff(c_5619,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_52,c_5583])).

tff(c_5621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5619])).

tff(c_5622,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5624,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5622])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5631,plain,(
    ! [B_208,A_209] :
      ( r1_tarski(B_208,k2_pre_topc(A_209,B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5638,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_5631])).

tff(c_5645,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5638])).

tff(c_5730,plain,(
    ! [A_224,B_225] :
      ( k1_tops_1(A_224,k2_pre_topc(A_224,B_225)) = B_225
      | ~ v6_tops_1(B_225,A_224)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5741,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_5730])).

tff(c_5750,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_5741])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k2_pre_topc(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5760,plain,(
    ! [B_226,A_227] :
      ( v5_tops_1(B_226,A_227)
      | k2_pre_topc(A_227,k1_tops_1(A_227,B_226)) != B_226
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5762,plain,
    ( v5_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5750,c_5760])).

tff(c_5769,plain,
    ( v5_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5762])).

tff(c_5774,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5769])).

tff(c_5777,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_5774])).

tff(c_5781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_5777])).

tff(c_5783,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_5769])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( k1_tops_1(A_23,k1_tops_1(A_23,B_24)) = k1_tops_1(A_23,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5831,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_5783,c_32])).

tff(c_5841,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5750,c_5750,c_5831])).

tff(c_6192,plain,(
    ! [B_260,A_261] :
      ( v4_tops_1(B_260,A_261)
      | ~ r1_tarski(B_260,k2_pre_topc(A_261,k1_tops_1(A_261,B_260)))
      | ~ r1_tarski(k1_tops_1(A_261,k2_pre_topc(A_261,B_260)),B_260)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6198,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5750,c_6192])).

tff(c_6201,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6,c_5645,c_5841,c_6198])).

tff(c_6203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5624,c_6201])).

tff(c_6204,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_5622])).

tff(c_6211,plain,(
    ! [B_264,A_265] :
      ( r1_tarski(B_264,k2_pre_topc(A_265,B_264))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6216,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_6211])).

tff(c_6222,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6216])).

tff(c_6616,plain,(
    ! [B_304,A_305,C_306] :
      ( r1_tarski(B_304,k1_tops_1(A_305,C_306))
      | ~ r1_tarski(B_304,C_306)
      | ~ v3_pre_topc(B_304,A_305)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9686,plain,(
    ! [B_389,A_390,B_391] :
      ( r1_tarski(B_389,k1_tops_1(A_390,k2_pre_topc(A_390,B_391)))
      | ~ r1_tarski(B_389,k2_pre_topc(A_390,B_391))
      | ~ v3_pre_topc(B_389,A_390)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ l1_pre_topc(A_390) ) ),
    inference(resolution,[status(thm)],[c_10,c_6616])).

tff(c_5623,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6205,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_5622])).

tff(c_56,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_6207,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5623,c_6205,c_56])).

tff(c_18,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k1_tops_1(A_10,k2_pre_topc(A_10,B_12)),B_12)
      | ~ v4_tops_1(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8306,plain,(
    ! [B_356,A_357,B_358] :
      ( r1_tarski(B_356,k1_tops_1(A_357,k2_pre_topc(A_357,B_358)))
      | ~ r1_tarski(B_356,k2_pre_topc(A_357,B_358))
      | ~ v3_pre_topc(B_356,A_357)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ l1_pre_topc(A_357) ) ),
    inference(resolution,[status(thm)],[c_10,c_6616])).

tff(c_6606,plain,(
    ! [A_300,B_301] :
      ( r1_tarski(k1_tops_1(A_300,k2_pre_topc(A_300,B_301)),B_301)
      | ~ v4_tops_1(B_301,A_300)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ l1_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6612,plain,(
    ! [A_300,B_301] :
      ( k1_tops_1(A_300,k2_pre_topc(A_300,B_301)) = B_301
      | ~ r1_tarski(B_301,k1_tops_1(A_300,k2_pre_topc(A_300,B_301)))
      | ~ v4_tops_1(B_301,A_300)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ l1_pre_topc(A_300) ) ),
    inference(resolution,[status(thm)],[c_6606,c_2])).

tff(c_8347,plain,(
    ! [A_359,B_360] :
      ( k1_tops_1(A_359,k2_pre_topc(A_359,B_360)) = B_360
      | ~ v4_tops_1(B_360,A_359)
      | ~ r1_tarski(B_360,k2_pre_topc(A_359,B_360))
      | ~ v3_pre_topc(B_360,A_359)
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ l1_pre_topc(A_359) ) ),
    inference(resolution,[status(thm)],[c_8306,c_6612])).

tff(c_8367,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6222,c_8347])).

tff(c_8388,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_6204,c_6207,c_8367])).

tff(c_6264,plain,(
    ! [A_272,B_273] :
      ( k1_tops_1(A_272,k1_tops_1(A_272,B_273)) = k1_tops_1(A_272,B_273)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6734,plain,(
    ! [A_314,B_315] :
      ( k1_tops_1(A_314,k1_tops_1(A_314,k2_pre_topc(A_314,B_315))) = k1_tops_1(A_314,k2_pre_topc(A_314,B_315))
      | ~ m1_subset_1(B_315,k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ l1_pre_topc(A_314) ) ),
    inference(resolution,[status(thm)],[c_10,c_6264])).

tff(c_6747,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_6734])).

tff(c_6761,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6747])).

tff(c_6238,plain,(
    ! [A_268,B_269] :
      ( m1_subset_1(k1_tops_1(A_268,B_269),k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( r1_tarski(B_9,k2_pre_topc(A_7,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6241,plain,(
    ! [A_268,B_269] :
      ( r1_tarski(k1_tops_1(A_268,B_269),k2_pre_topc(A_268,k1_tops_1(A_268,B_269)))
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268) ) ),
    inference(resolution,[status(thm)],[c_6238,c_12])).

tff(c_6771,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6761,c_6241])).

tff(c_6788,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6761,c_6771])).

tff(c_7094,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6788])).

tff(c_7097,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_7094])).

tff(c_7100,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7097])).

tff(c_7103,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_7100])).

tff(c_7107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_7103])).

tff(c_7109,plain,(
    m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6788])).

tff(c_6629,plain,(
    ! [B_304] :
      ( r1_tarski(B_304,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_304,'#skF_4')
      | ~ v3_pre_topc(B_304,'#skF_2')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_6616])).

tff(c_6643,plain,(
    ! [B_304] :
      ( r1_tarski(B_304,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_304,'#skF_4')
      | ~ v3_pre_topc(B_304,'#skF_2')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6629])).

tff(c_7155,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7109,c_6643])).

tff(c_7185,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7155])).

tff(c_8393,plain,(
    ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8388,c_7185])).

tff(c_8400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6204,c_8393])).

tff(c_8401,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4')
    | r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7155])).

tff(c_8403,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8401])).

tff(c_8406,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_8403])).

tff(c_8410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_6207,c_8406])).

tff(c_8412,plain,(
    r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8401])).

tff(c_8421,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_8412,c_2])).

tff(c_8425,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_8421])).

tff(c_9703,plain,
    ( ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_9686,c_8425])).

tff(c_9734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_6204,c_6222,c_9703])).

tff(c_9735,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8421])).

tff(c_24,plain,(
    ! [B_18,A_16] :
      ( v6_tops_1(B_18,A_16)
      | k1_tops_1(A_16,k2_pre_topc(A_16,B_18)) != B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9775,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9735,c_24])).

tff(c_9801,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_9775])).

tff(c_9803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_9801])).

tff(c_9804,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_9817,plain,(
    ! [B_396,A_397] :
      ( r1_tarski(B_396,k2_pre_topc(A_397,B_396))
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ l1_pre_topc(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_9822,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_9817])).

tff(c_9828,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_9822])).

tff(c_10135,plain,(
    ! [B_430,A_431,C_432] :
      ( r1_tarski(B_430,k1_tops_1(A_431,C_432))
      | ~ r1_tarski(B_430,C_432)
      | ~ v3_pre_topc(B_430,A_431)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(u1_struct_0(A_431)))
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0(A_431)))
      | ~ l1_pre_topc(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12218,plain,(
    ! [B_496,A_497,B_498] :
      ( r1_tarski(B_496,k1_tops_1(A_497,k2_pre_topc(A_497,B_498)))
      | ~ r1_tarski(B_496,k2_pre_topc(A_497,B_498))
      | ~ v3_pre_topc(B_496,A_497)
      | ~ m1_subset_1(B_496,k1_zfmisc_1(u1_struct_0(A_497)))
      | ~ m1_subset_1(B_498,k1_zfmisc_1(u1_struct_0(A_497)))
      | ~ l1_pre_topc(A_497) ) ),
    inference(resolution,[status(thm)],[c_10,c_10135])).

tff(c_9805,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_9806,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_9805,c_62])).

tff(c_11536,plain,(
    ! [B_480,A_481,B_482] :
      ( r1_tarski(B_480,k1_tops_1(A_481,k2_pre_topc(A_481,B_482)))
      | ~ r1_tarski(B_480,k2_pre_topc(A_481,B_482))
      | ~ v3_pre_topc(B_480,A_481)
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0(A_481)))
      | ~ m1_subset_1(B_482,k1_zfmisc_1(u1_struct_0(A_481)))
      | ~ l1_pre_topc(A_481) ) ),
    inference(resolution,[status(thm)],[c_10,c_10135])).

tff(c_10122,plain,(
    ! [A_428,B_429] :
      ( r1_tarski(k1_tops_1(A_428,k2_pre_topc(A_428,B_429)),B_429)
      | ~ v4_tops_1(B_429,A_428)
      | ~ m1_subset_1(B_429,k1_zfmisc_1(u1_struct_0(A_428)))
      | ~ l1_pre_topc(A_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10125,plain,(
    ! [A_428,B_429] :
      ( k1_tops_1(A_428,k2_pre_topc(A_428,B_429)) = B_429
      | ~ r1_tarski(B_429,k1_tops_1(A_428,k2_pre_topc(A_428,B_429)))
      | ~ v4_tops_1(B_429,A_428)
      | ~ m1_subset_1(B_429,k1_zfmisc_1(u1_struct_0(A_428)))
      | ~ l1_pre_topc(A_428) ) ),
    inference(resolution,[status(thm)],[c_10122,c_2])).

tff(c_12040,plain,(
    ! [A_491,B_492] :
      ( k1_tops_1(A_491,k2_pre_topc(A_491,B_492)) = B_492
      | ~ v4_tops_1(B_492,A_491)
      | ~ r1_tarski(B_492,k2_pre_topc(A_491,B_492))
      | ~ v3_pre_topc(B_492,A_491)
      | ~ m1_subset_1(B_492,k1_zfmisc_1(u1_struct_0(A_491)))
      | ~ l1_pre_topc(A_491) ) ),
    inference(resolution,[status(thm)],[c_11536,c_10125])).

tff(c_12062,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_9828,c_12040])).

tff(c_12086,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_9804,c_9806,c_12062])).

tff(c_9869,plain,(
    ! [A_404,B_405] :
      ( k1_tops_1(A_404,k1_tops_1(A_404,B_405)) = k1_tops_1(A_404,B_405)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10290,plain,(
    ! [A_448,B_449] :
      ( k1_tops_1(A_448,k1_tops_1(A_448,k2_pre_topc(A_448,B_449))) = k1_tops_1(A_448,k2_pre_topc(A_448,B_449))
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ l1_pre_topc(A_448) ) ),
    inference(resolution,[status(thm)],[c_10,c_9869])).

tff(c_10303,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_10290])).

tff(c_10317,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10303])).

tff(c_9844,plain,(
    ! [A_400,B_401] :
      ( m1_subset_1(k1_tops_1(A_400,B_401),k1_zfmisc_1(u1_struct_0(A_400)))
      | ~ m1_subset_1(B_401,k1_zfmisc_1(u1_struct_0(A_400)))
      | ~ l1_pre_topc(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9847,plain,(
    ! [A_400,B_401] :
      ( r1_tarski(k1_tops_1(A_400,B_401),k2_pre_topc(A_400,k1_tops_1(A_400,B_401)))
      | ~ m1_subset_1(B_401,k1_zfmisc_1(u1_struct_0(A_400)))
      | ~ l1_pre_topc(A_400) ) ),
    inference(resolution,[status(thm)],[c_9844,c_12])).

tff(c_10333,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))),k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10317,c_9847])).

tff(c_10348,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10317,c_10333])).

tff(c_10991,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_10348])).

tff(c_10995,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_10991])).

tff(c_10998,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10995])).

tff(c_11001,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_10998])).

tff(c_11005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_11001])).

tff(c_11007,plain,(
    m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_10348])).

tff(c_10148,plain,(
    ! [B_430] :
      ( r1_tarski(B_430,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_430,'#skF_4')
      | ~ v3_pre_topc(B_430,'#skF_2')
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_10135])).

tff(c_10162,plain,(
    ! [B_430] :
      ( r1_tarski(B_430,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_430,'#skF_4')
      | ~ v3_pre_topc(B_430,'#skF_2')
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10148])).

tff(c_11053,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_11007,c_10162])).

tff(c_11139,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_11053])).

tff(c_12089,plain,(
    ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12086,c_11139])).

tff(c_12096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9804,c_12089])).

tff(c_12097,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4')
    | r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11053])).

tff(c_12192,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12097])).

tff(c_12195,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_12192])).

tff(c_12199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_9806,c_12195])).

tff(c_12201,plain,(
    r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_12097])).

tff(c_12210,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_12201,c_2])).

tff(c_12216,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_12210])).

tff(c_12224,plain,
    ( ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12218,c_12216])).

tff(c_12251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_9804,c_9828,c_12224])).

tff(c_12252,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12210])).

tff(c_12300,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12252,c_24])).

tff(c_12332,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_12300])).

tff(c_12334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_12332])).

tff(c_12335,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_12614,plain,(
    ! [A_523,B_524] :
      ( k2_pre_topc(A_523,k1_tops_1(A_523,B_524)) = B_524
      | ~ v5_tops_1(B_524,A_523)
      | ~ m1_subset_1(B_524,k1_zfmisc_1(u1_struct_0(A_523)))
      | ~ l1_pre_topc(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_13664,plain,(
    ! [A_582,B_583] :
      ( k2_pre_topc(A_582,k1_tops_1(A_582,k3_subset_1(u1_struct_0(A_582),B_583))) = k3_subset_1(u1_struct_0(A_582),B_583)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_582),B_583),A_582)
      | ~ l1_pre_topc(A_582)
      | ~ m1_subset_1(B_583,k1_zfmisc_1(u1_struct_0(A_582))) ) ),
    inference(resolution,[status(thm)],[c_8,c_12614])).

tff(c_12396,plain,(
    ! [A_509,B_510] :
      ( m1_subset_1(k1_tops_1(A_509,B_510),k1_zfmisc_1(u1_struct_0(A_509)))
      | ~ m1_subset_1(B_510,k1_zfmisc_1(u1_struct_0(A_509)))
      | ~ l1_pre_topc(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( v4_pre_topc(k2_pre_topc(A_21,B_22),A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12401,plain,(
    ! [A_509,B_510] :
      ( v4_pre_topc(k2_pre_topc(A_509,k1_tops_1(A_509,B_510)),A_509)
      | ~ v2_pre_topc(A_509)
      | ~ m1_subset_1(B_510,k1_zfmisc_1(u1_struct_0(A_509)))
      | ~ l1_pre_topc(A_509) ) ),
    inference(resolution,[status(thm)],[c_12396,c_30])).

tff(c_16674,plain,(
    ! [A_645,B_646] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_645),B_646),A_645)
      | ~ v2_pre_topc(A_645)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_645),B_646),k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ l1_pre_topc(A_645)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_645),B_646),A_645)
      | ~ l1_pre_topc(A_645)
      | ~ m1_subset_1(B_646,k1_zfmisc_1(u1_struct_0(A_645))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13664,c_12401])).

tff(c_16680,plain,(
    ! [A_647,B_648] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_647),B_648),A_647)
      | ~ v2_pre_topc(A_647)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_647),B_648),A_647)
      | ~ l1_pre_topc(A_647)
      | ~ m1_subset_1(B_648,k1_zfmisc_1(u1_struct_0(A_647))) ) ),
    inference(resolution,[status(thm)],[c_8,c_16674])).

tff(c_16685,plain,(
    ! [A_649,B_650] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_649),B_650),A_649)
      | ~ v2_pre_topc(A_649)
      | ~ v6_tops_1(B_650,A_649)
      | ~ m1_subset_1(B_650,k1_zfmisc_1(u1_struct_0(A_649)))
      | ~ l1_pre_topc(A_649) ) ),
    inference(resolution,[status(thm)],[c_36,c_16680])).

tff(c_16796,plain,(
    ! [B_654,A_655] :
      ( v3_pre_topc(B_654,A_655)
      | ~ v2_pre_topc(A_655)
      | ~ v6_tops_1(B_654,A_655)
      | ~ m1_subset_1(B_654,k1_zfmisc_1(u1_struct_0(A_655)))
      | ~ l1_pre_topc(A_655) ) ),
    inference(resolution,[status(thm)],[c_16685,c_38])).

tff(c_16827,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_16796])).

tff(c_16856,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12335,c_52,c_16827])).

tff(c_16858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12346,c_16856])).

tff(c_16860,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16859,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16861,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16859])).

tff(c_16868,plain,(
    ! [B_658,A_659] :
      ( r1_tarski(B_658,k2_pre_topc(A_659,B_658))
      | ~ m1_subset_1(B_658,k1_zfmisc_1(u1_struct_0(A_659)))
      | ~ l1_pre_topc(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16875,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_16868])).

tff(c_16882,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16875])).

tff(c_16967,plain,(
    ! [A_674,B_675] :
      ( k1_tops_1(A_674,k2_pre_topc(A_674,B_675)) = B_675
      | ~ v6_tops_1(B_675,A_674)
      | ~ m1_subset_1(B_675,k1_zfmisc_1(u1_struct_0(A_674)))
      | ~ l1_pre_topc(A_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16978,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_16967])).

tff(c_16987,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12335,c_16978])).

tff(c_20,plain,(
    ! [B_15,A_13] :
      ( v5_tops_1(B_15,A_13)
      | k2_pre_topc(A_13,k1_tops_1(A_13,B_15)) != B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_17013,plain,
    ( v5_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16987,c_20])).

tff(c_17021,plain,
    ( v5_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_17013])).

tff(c_17035,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_17021])).

tff(c_17072,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_17035])).

tff(c_17076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_17072])).

tff(c_17078,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_17021])).

tff(c_17105,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17078,c_32])).

tff(c_17118,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16987,c_16987,c_17105])).

tff(c_17426,plain,(
    ! [B_705,A_706] :
      ( v4_tops_1(B_705,A_706)
      | ~ r1_tarski(B_705,k2_pre_topc(A_706,k1_tops_1(A_706,B_705)))
      | ~ r1_tarski(k1_tops_1(A_706,k2_pre_topc(A_706,B_705)),B_705)
      | ~ m1_subset_1(B_705,k1_zfmisc_1(u1_struct_0(A_706)))
      | ~ l1_pre_topc(A_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_17432,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16987,c_17426])).

tff(c_17438,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6,c_16882,c_17118,c_17432])).

tff(c_17440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16861,c_17438])).

tff(c_17442,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_16859])).

tff(c_12336,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_17446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16860,c_17442,c_12336,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:32 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.17/4.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.23/4.06  
% 11.23/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.23/4.06  %$ v6_tops_1 > v5_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.23/4.06  
% 11.23/4.06  %Foreground sorts:
% 11.23/4.06  
% 11.23/4.06  
% 11.23/4.06  %Background operators:
% 11.23/4.06  
% 11.23/4.06  
% 11.23/4.06  %Foreground operators:
% 11.23/4.06  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.23/4.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.23/4.06  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 11.23/4.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.23/4.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.23/4.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.23/4.06  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 11.23/4.06  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.23/4.06  tff('#skF_2', type, '#skF_2': $i).
% 11.23/4.06  tff('#skF_3', type, '#skF_3': $i).
% 11.23/4.06  tff('#skF_1', type, '#skF_1': $i).
% 11.23/4.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.23/4.06  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.23/4.06  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 11.23/4.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.23/4.06  tff('#skF_4', type, '#skF_4': $i).
% 11.23/4.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.23/4.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.23/4.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.23/4.06  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.23/4.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.23/4.06  
% 11.23/4.09  tff(f_155, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 11.23/4.09  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> v5_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_tops_1)).
% 11.23/4.09  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.23/4.09  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 11.23/4.09  tff(f_83, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 11.23/4.09  tff(f_91, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 11.23/4.09  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 11.23/4.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.23/4.09  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 11.23/4.09  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 11.23/4.09  tff(f_41, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.23/4.09  tff(f_97, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 11.23/4.09  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 11.23/4.09  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 11.23/4.09  tff(c_58, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_12346, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 11.23/4.09  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_60, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_67, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 11.23/4.09  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_78, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 11.23/4.09  tff(c_64, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_68, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 11.23/4.09  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_36, plain, (![A_25, B_27]: (v5_tops_1(k3_subset_1(u1_struct_0(A_25), B_27), A_25) | ~v6_tops_1(B_27, A_25) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.23/4.09  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.23/4.09  tff(c_210, plain, (![A_72, B_73]: (k2_pre_topc(A_72, k1_tops_1(A_72, B_73))=B_73 | ~v5_tops_1(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.23/4.09  tff(c_1760, plain, (![A_136, B_137]: (k2_pre_topc(A_136, k1_tops_1(A_136, k3_subset_1(u1_struct_0(A_136), B_137)))=k3_subset_1(u1_struct_0(A_136), B_137) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_136), B_137), A_136) | ~l1_pre_topc(A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))))), inference(resolution, [status(thm)], [c_8, c_210])).
% 11.23/4.09  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k1_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.23/4.09  tff(c_107, plain, (![A_58, B_59]: (v4_pre_topc(k2_pre_topc(A_58, B_59), A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.23/4.09  tff(c_117, plain, (![A_19, B_20]: (v4_pre_topc(k2_pre_topc(A_19, k1_tops_1(A_19, B_20)), A_19) | ~v2_pre_topc(A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(resolution, [status(thm)], [c_28, c_107])).
% 11.23/4.09  tff(c_5404, plain, (![A_196, B_197]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_196), B_197), A_196) | ~v2_pre_topc(A_196) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_196), B_197), k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_196), B_197), A_196) | ~l1_pre_topc(A_196) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))))), inference(superposition, [status(thm), theory('equality')], [c_1760, c_117])).
% 11.23/4.09  tff(c_5410, plain, (![A_198, B_199]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_198), B_199), A_198) | ~v2_pre_topc(A_198) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_198), B_199), A_198) | ~l1_pre_topc(A_198) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))))), inference(resolution, [status(thm)], [c_8, c_5404])).
% 11.23/4.09  tff(c_5415, plain, (![A_200, B_201]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_200), B_201), A_200) | ~v2_pre_topc(A_200) | ~v6_tops_1(B_201, A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(resolution, [status(thm)], [c_36, c_5410])).
% 11.23/4.09  tff(c_38, plain, (![B_30, A_28]: (v3_pre_topc(B_30, A_28) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_28), B_30), A_28) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.23/4.09  tff(c_5546, plain, (![B_204, A_205]: (v3_pre_topc(B_204, A_205) | ~v2_pre_topc(A_205) | ~v6_tops_1(B_204, A_205) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(resolution, [status(thm)], [c_5415, c_38])).
% 11.23/4.09  tff(c_5583, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_5546])).
% 11.23/4.09  tff(c_5619, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_52, c_5583])).
% 11.23/4.09  tff(c_5621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5619])).
% 11.23/4.09  tff(c_5622, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 11.23/4.09  tff(c_5624, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_5622])).
% 11.23/4.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.23/4.09  tff(c_5631, plain, (![B_208, A_209]: (r1_tarski(B_208, k2_pre_topc(A_209, B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.23/4.09  tff(c_5638, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_5631])).
% 11.23/4.09  tff(c_5645, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5638])).
% 11.23/4.09  tff(c_5730, plain, (![A_224, B_225]: (k1_tops_1(A_224, k2_pre_topc(A_224, B_225))=B_225 | ~v6_tops_1(B_225, A_224) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.23/4.09  tff(c_5741, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_5730])).
% 11.23/4.09  tff(c_5750, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_5741])).
% 11.23/4.09  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k2_pre_topc(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.23/4.09  tff(c_5760, plain, (![B_226, A_227]: (v5_tops_1(B_226, A_227) | k2_pre_topc(A_227, k1_tops_1(A_227, B_226))!=B_226 | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.23/4.09  tff(c_5762, plain, (v5_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5750, c_5760])).
% 11.23/4.09  tff(c_5769, plain, (v5_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5762])).
% 11.23/4.09  tff(c_5774, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_5769])).
% 11.23/4.09  tff(c_5777, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_5774])).
% 11.23/4.09  tff(c_5781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_5777])).
% 11.23/4.09  tff(c_5783, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_5769])).
% 11.23/4.09  tff(c_32, plain, (![A_23, B_24]: (k1_tops_1(A_23, k1_tops_1(A_23, B_24))=k1_tops_1(A_23, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.23/4.09  tff(c_5831, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_5783, c_32])).
% 11.23/4.09  tff(c_5841, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5750, c_5750, c_5831])).
% 11.23/4.09  tff(c_6192, plain, (![B_260, A_261]: (v4_tops_1(B_260, A_261) | ~r1_tarski(B_260, k2_pre_topc(A_261, k1_tops_1(A_261, B_260))) | ~r1_tarski(k1_tops_1(A_261, k2_pre_topc(A_261, B_260)), B_260) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.23/4.09  tff(c_6198, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5750, c_6192])).
% 11.23/4.09  tff(c_6201, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6, c_5645, c_5841, c_6198])).
% 11.23/4.09  tff(c_6203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5624, c_6201])).
% 11.23/4.09  tff(c_6204, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_5622])).
% 11.23/4.09  tff(c_6211, plain, (![B_264, A_265]: (r1_tarski(B_264, k2_pre_topc(A_265, B_264)) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.23/4.09  tff(c_6216, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_6211])).
% 11.23/4.09  tff(c_6222, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6216])).
% 11.23/4.09  tff(c_6616, plain, (![B_304, A_305, C_306]: (r1_tarski(B_304, k1_tops_1(A_305, C_306)) | ~r1_tarski(B_304, C_306) | ~v3_pre_topc(B_304, A_305) | ~m1_subset_1(C_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.23/4.09  tff(c_9686, plain, (![B_389, A_390, B_391]: (r1_tarski(B_389, k1_tops_1(A_390, k2_pre_topc(A_390, B_391))) | ~r1_tarski(B_389, k2_pre_topc(A_390, B_391)) | ~v3_pre_topc(B_389, A_390) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_390))) | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0(A_390))) | ~l1_pre_topc(A_390))), inference(resolution, [status(thm)], [c_10, c_6616])).
% 11.23/4.09  tff(c_5623, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 11.23/4.09  tff(c_6205, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_5622])).
% 11.23/4.09  tff(c_56, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_6207, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5623, c_6205, c_56])).
% 11.23/4.09  tff(c_18, plain, (![A_10, B_12]: (r1_tarski(k1_tops_1(A_10, k2_pre_topc(A_10, B_12)), B_12) | ~v4_tops_1(B_12, A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.23/4.09  tff(c_8306, plain, (![B_356, A_357, B_358]: (r1_tarski(B_356, k1_tops_1(A_357, k2_pre_topc(A_357, B_358))) | ~r1_tarski(B_356, k2_pre_topc(A_357, B_358)) | ~v3_pre_topc(B_356, A_357) | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0(A_357))) | ~m1_subset_1(B_358, k1_zfmisc_1(u1_struct_0(A_357))) | ~l1_pre_topc(A_357))), inference(resolution, [status(thm)], [c_10, c_6616])).
% 11.23/4.09  tff(c_6606, plain, (![A_300, B_301]: (r1_tarski(k1_tops_1(A_300, k2_pre_topc(A_300, B_301)), B_301) | ~v4_tops_1(B_301, A_300) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_300))) | ~l1_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.23/4.09  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.23/4.09  tff(c_6612, plain, (![A_300, B_301]: (k1_tops_1(A_300, k2_pre_topc(A_300, B_301))=B_301 | ~r1_tarski(B_301, k1_tops_1(A_300, k2_pre_topc(A_300, B_301))) | ~v4_tops_1(B_301, A_300) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_300))) | ~l1_pre_topc(A_300))), inference(resolution, [status(thm)], [c_6606, c_2])).
% 11.23/4.09  tff(c_8347, plain, (![A_359, B_360]: (k1_tops_1(A_359, k2_pre_topc(A_359, B_360))=B_360 | ~v4_tops_1(B_360, A_359) | ~r1_tarski(B_360, k2_pre_topc(A_359, B_360)) | ~v3_pre_topc(B_360, A_359) | ~m1_subset_1(B_360, k1_zfmisc_1(u1_struct_0(A_359))) | ~l1_pre_topc(A_359))), inference(resolution, [status(thm)], [c_8306, c_6612])).
% 11.23/4.09  tff(c_8367, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6222, c_8347])).
% 11.23/4.09  tff(c_8388, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_6204, c_6207, c_8367])).
% 11.23/4.09  tff(c_6264, plain, (![A_272, B_273]: (k1_tops_1(A_272, k1_tops_1(A_272, B_273))=k1_tops_1(A_272, B_273) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_pre_topc(A_272))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.23/4.09  tff(c_6734, plain, (![A_314, B_315]: (k1_tops_1(A_314, k1_tops_1(A_314, k2_pre_topc(A_314, B_315)))=k1_tops_1(A_314, k2_pre_topc(A_314, B_315)) | ~m1_subset_1(B_315, k1_zfmisc_1(u1_struct_0(A_314))) | ~l1_pre_topc(A_314))), inference(resolution, [status(thm)], [c_10, c_6264])).
% 11.23/4.09  tff(c_6747, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_6734])).
% 11.23/4.09  tff(c_6761, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6747])).
% 11.23/4.09  tff(c_6238, plain, (![A_268, B_269]: (m1_subset_1(k1_tops_1(A_268, B_269), k1_zfmisc_1(u1_struct_0(A_268))) | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_pre_topc(A_268))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.23/4.09  tff(c_12, plain, (![B_9, A_7]: (r1_tarski(B_9, k2_pre_topc(A_7, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.23/4.09  tff(c_6241, plain, (![A_268, B_269]: (r1_tarski(k1_tops_1(A_268, B_269), k2_pre_topc(A_268, k1_tops_1(A_268, B_269))) | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_pre_topc(A_268))), inference(resolution, [status(thm)], [c_6238, c_12])).
% 11.23/4.09  tff(c_6771, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6761, c_6241])).
% 11.23/4.09  tff(c_6788, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6761, c_6771])).
% 11.23/4.09  tff(c_7094, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_6788])).
% 11.23/4.09  tff(c_7097, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_7094])).
% 11.23/4.09  tff(c_7100, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7097])).
% 11.23/4.09  tff(c_7103, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_7100])).
% 11.23/4.09  tff(c_7107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_7103])).
% 11.23/4.09  tff(c_7109, plain, (m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_6788])).
% 11.23/4.09  tff(c_6629, plain, (![B_304]: (r1_tarski(B_304, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_304, '#skF_4') | ~v3_pre_topc(B_304, '#skF_2') | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_6616])).
% 11.23/4.09  tff(c_6643, plain, (![B_304]: (r1_tarski(B_304, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_304, '#skF_4') | ~v3_pre_topc(B_304, '#skF_2') | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6629])).
% 11.23/4.09  tff(c_7155, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_7109, c_6643])).
% 11.23/4.09  tff(c_7185, plain, (~v3_pre_topc(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_7155])).
% 11.23/4.09  tff(c_8393, plain, (~v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8388, c_7185])).
% 11.23/4.09  tff(c_8400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6204, c_8393])).
% 11.23/4.09  tff(c_8401, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4') | r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_7155])).
% 11.23/4.09  tff(c_8403, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_8401])).
% 11.23/4.09  tff(c_8406, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_8403])).
% 11.23/4.09  tff(c_8410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_6207, c_8406])).
% 11.23/4.09  tff(c_8412, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_8401])).
% 11.23/4.09  tff(c_8421, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_8412, c_2])).
% 11.23/4.09  tff(c_8425, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(splitLeft, [status(thm)], [c_8421])).
% 11.23/4.09  tff(c_9703, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_9686, c_8425])).
% 11.23/4.09  tff(c_9734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_6204, c_6222, c_9703])).
% 11.23/4.09  tff(c_9735, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_8421])).
% 11.23/4.09  tff(c_24, plain, (![B_18, A_16]: (v6_tops_1(B_18, A_16) | k1_tops_1(A_16, k2_pre_topc(A_16, B_18))!=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.23/4.09  tff(c_9775, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9735, c_24])).
% 11.23/4.09  tff(c_9801, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_9775])).
% 11.23/4.09  tff(c_9803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_9801])).
% 11.23/4.09  tff(c_9804, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 11.23/4.09  tff(c_9817, plain, (![B_396, A_397]: (r1_tarski(B_396, k2_pre_topc(A_397, B_396)) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_397))) | ~l1_pre_topc(A_397))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.23/4.09  tff(c_9822, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_9817])).
% 11.23/4.09  tff(c_9828, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_9822])).
% 11.23/4.09  tff(c_10135, plain, (![B_430, A_431, C_432]: (r1_tarski(B_430, k1_tops_1(A_431, C_432)) | ~r1_tarski(B_430, C_432) | ~v3_pre_topc(B_430, A_431) | ~m1_subset_1(C_432, k1_zfmisc_1(u1_struct_0(A_431))) | ~m1_subset_1(B_430, k1_zfmisc_1(u1_struct_0(A_431))) | ~l1_pre_topc(A_431))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.23/4.09  tff(c_12218, plain, (![B_496, A_497, B_498]: (r1_tarski(B_496, k1_tops_1(A_497, k2_pre_topc(A_497, B_498))) | ~r1_tarski(B_496, k2_pre_topc(A_497, B_498)) | ~v3_pre_topc(B_496, A_497) | ~m1_subset_1(B_496, k1_zfmisc_1(u1_struct_0(A_497))) | ~m1_subset_1(B_498, k1_zfmisc_1(u1_struct_0(A_497))) | ~l1_pre_topc(A_497))), inference(resolution, [status(thm)], [c_10, c_10135])).
% 11.23/4.09  tff(c_9805, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 11.23/4.09  tff(c_62, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_9806, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_9805, c_62])).
% 11.23/4.09  tff(c_11536, plain, (![B_480, A_481, B_482]: (r1_tarski(B_480, k1_tops_1(A_481, k2_pre_topc(A_481, B_482))) | ~r1_tarski(B_480, k2_pre_topc(A_481, B_482)) | ~v3_pre_topc(B_480, A_481) | ~m1_subset_1(B_480, k1_zfmisc_1(u1_struct_0(A_481))) | ~m1_subset_1(B_482, k1_zfmisc_1(u1_struct_0(A_481))) | ~l1_pre_topc(A_481))), inference(resolution, [status(thm)], [c_10, c_10135])).
% 11.23/4.09  tff(c_10122, plain, (![A_428, B_429]: (r1_tarski(k1_tops_1(A_428, k2_pre_topc(A_428, B_429)), B_429) | ~v4_tops_1(B_429, A_428) | ~m1_subset_1(B_429, k1_zfmisc_1(u1_struct_0(A_428))) | ~l1_pre_topc(A_428))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.23/4.09  tff(c_10125, plain, (![A_428, B_429]: (k1_tops_1(A_428, k2_pre_topc(A_428, B_429))=B_429 | ~r1_tarski(B_429, k1_tops_1(A_428, k2_pre_topc(A_428, B_429))) | ~v4_tops_1(B_429, A_428) | ~m1_subset_1(B_429, k1_zfmisc_1(u1_struct_0(A_428))) | ~l1_pre_topc(A_428))), inference(resolution, [status(thm)], [c_10122, c_2])).
% 11.23/4.09  tff(c_12040, plain, (![A_491, B_492]: (k1_tops_1(A_491, k2_pre_topc(A_491, B_492))=B_492 | ~v4_tops_1(B_492, A_491) | ~r1_tarski(B_492, k2_pre_topc(A_491, B_492)) | ~v3_pre_topc(B_492, A_491) | ~m1_subset_1(B_492, k1_zfmisc_1(u1_struct_0(A_491))) | ~l1_pre_topc(A_491))), inference(resolution, [status(thm)], [c_11536, c_10125])).
% 11.23/4.09  tff(c_12062, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_9828, c_12040])).
% 11.23/4.09  tff(c_12086, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_9804, c_9806, c_12062])).
% 11.23/4.09  tff(c_9869, plain, (![A_404, B_405]: (k1_tops_1(A_404, k1_tops_1(A_404, B_405))=k1_tops_1(A_404, B_405) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.23/4.09  tff(c_10290, plain, (![A_448, B_449]: (k1_tops_1(A_448, k1_tops_1(A_448, k2_pre_topc(A_448, B_449)))=k1_tops_1(A_448, k2_pre_topc(A_448, B_449)) | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0(A_448))) | ~l1_pre_topc(A_448))), inference(resolution, [status(thm)], [c_10, c_9869])).
% 11.23/4.09  tff(c_10303, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_10290])).
% 11.23/4.09  tff(c_10317, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10303])).
% 11.23/4.09  tff(c_9844, plain, (![A_400, B_401]: (m1_subset_1(k1_tops_1(A_400, B_401), k1_zfmisc_1(u1_struct_0(A_400))) | ~m1_subset_1(B_401, k1_zfmisc_1(u1_struct_0(A_400))) | ~l1_pre_topc(A_400))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.23/4.09  tff(c_9847, plain, (![A_400, B_401]: (r1_tarski(k1_tops_1(A_400, B_401), k2_pre_topc(A_400, k1_tops_1(A_400, B_401))) | ~m1_subset_1(B_401, k1_zfmisc_1(u1_struct_0(A_400))) | ~l1_pre_topc(A_400))), inference(resolution, [status(thm)], [c_9844, c_12])).
% 11.23/4.09  tff(c_10333, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10317, c_9847])).
% 11.23/4.09  tff(c_10348, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10317, c_10333])).
% 11.23/4.09  tff(c_10991, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_10348])).
% 11.23/4.09  tff(c_10995, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_10991])).
% 11.23/4.09  tff(c_10998, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10995])).
% 11.23/4.09  tff(c_11001, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_10998])).
% 11.23/4.09  tff(c_11005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_11001])).
% 11.23/4.09  tff(c_11007, plain, (m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_10348])).
% 11.23/4.09  tff(c_10148, plain, (![B_430]: (r1_tarski(B_430, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_430, '#skF_4') | ~v3_pre_topc(B_430, '#skF_2') | ~m1_subset_1(B_430, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_10135])).
% 11.23/4.09  tff(c_10162, plain, (![B_430]: (r1_tarski(B_430, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_430, '#skF_4') | ~v3_pre_topc(B_430, '#skF_2') | ~m1_subset_1(B_430, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10148])).
% 11.23/4.09  tff(c_11053, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_11007, c_10162])).
% 11.23/4.09  tff(c_11139, plain, (~v3_pre_topc(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_11053])).
% 11.23/4.09  tff(c_12089, plain, (~v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12086, c_11139])).
% 11.23/4.09  tff(c_12096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9804, c_12089])).
% 11.23/4.09  tff(c_12097, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4') | r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_11053])).
% 11.23/4.09  tff(c_12192, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_12097])).
% 11.23/4.09  tff(c_12195, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_12192])).
% 11.23/4.09  tff(c_12199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_9806, c_12195])).
% 11.23/4.09  tff(c_12201, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_12097])).
% 11.23/4.09  tff(c_12210, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_12201, c_2])).
% 11.23/4.09  tff(c_12216, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(splitLeft, [status(thm)], [c_12210])).
% 11.23/4.09  tff(c_12224, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12218, c_12216])).
% 11.23/4.09  tff(c_12251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_9804, c_9828, c_12224])).
% 11.23/4.09  tff(c_12252, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_12210])).
% 11.23/4.09  tff(c_12300, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12252, c_24])).
% 11.23/4.09  tff(c_12332, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_12300])).
% 11.23/4.09  tff(c_12334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_12332])).
% 11.23/4.09  tff(c_12335, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_60])).
% 11.23/4.09  tff(c_12614, plain, (![A_523, B_524]: (k2_pre_topc(A_523, k1_tops_1(A_523, B_524))=B_524 | ~v5_tops_1(B_524, A_523) | ~m1_subset_1(B_524, k1_zfmisc_1(u1_struct_0(A_523))) | ~l1_pre_topc(A_523))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.23/4.09  tff(c_13664, plain, (![A_582, B_583]: (k2_pre_topc(A_582, k1_tops_1(A_582, k3_subset_1(u1_struct_0(A_582), B_583)))=k3_subset_1(u1_struct_0(A_582), B_583) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_582), B_583), A_582) | ~l1_pre_topc(A_582) | ~m1_subset_1(B_583, k1_zfmisc_1(u1_struct_0(A_582))))), inference(resolution, [status(thm)], [c_8, c_12614])).
% 11.23/4.09  tff(c_12396, plain, (![A_509, B_510]: (m1_subset_1(k1_tops_1(A_509, B_510), k1_zfmisc_1(u1_struct_0(A_509))) | ~m1_subset_1(B_510, k1_zfmisc_1(u1_struct_0(A_509))) | ~l1_pre_topc(A_509))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.23/4.09  tff(c_30, plain, (![A_21, B_22]: (v4_pre_topc(k2_pre_topc(A_21, B_22), A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.23/4.09  tff(c_12401, plain, (![A_509, B_510]: (v4_pre_topc(k2_pre_topc(A_509, k1_tops_1(A_509, B_510)), A_509) | ~v2_pre_topc(A_509) | ~m1_subset_1(B_510, k1_zfmisc_1(u1_struct_0(A_509))) | ~l1_pre_topc(A_509))), inference(resolution, [status(thm)], [c_12396, c_30])).
% 11.23/4.09  tff(c_16674, plain, (![A_645, B_646]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_645), B_646), A_645) | ~v2_pre_topc(A_645) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_645), B_646), k1_zfmisc_1(u1_struct_0(A_645))) | ~l1_pre_topc(A_645) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_645), B_646), A_645) | ~l1_pre_topc(A_645) | ~m1_subset_1(B_646, k1_zfmisc_1(u1_struct_0(A_645))))), inference(superposition, [status(thm), theory('equality')], [c_13664, c_12401])).
% 11.23/4.09  tff(c_16680, plain, (![A_647, B_648]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_647), B_648), A_647) | ~v2_pre_topc(A_647) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_647), B_648), A_647) | ~l1_pre_topc(A_647) | ~m1_subset_1(B_648, k1_zfmisc_1(u1_struct_0(A_647))))), inference(resolution, [status(thm)], [c_8, c_16674])).
% 11.23/4.09  tff(c_16685, plain, (![A_649, B_650]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_649), B_650), A_649) | ~v2_pre_topc(A_649) | ~v6_tops_1(B_650, A_649) | ~m1_subset_1(B_650, k1_zfmisc_1(u1_struct_0(A_649))) | ~l1_pre_topc(A_649))), inference(resolution, [status(thm)], [c_36, c_16680])).
% 11.23/4.09  tff(c_16796, plain, (![B_654, A_655]: (v3_pre_topc(B_654, A_655) | ~v2_pre_topc(A_655) | ~v6_tops_1(B_654, A_655) | ~m1_subset_1(B_654, k1_zfmisc_1(u1_struct_0(A_655))) | ~l1_pre_topc(A_655))), inference(resolution, [status(thm)], [c_16685, c_38])).
% 11.23/4.09  tff(c_16827, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_16796])).
% 11.23/4.09  tff(c_16856, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12335, c_52, c_16827])).
% 11.23/4.09  tff(c_16858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12346, c_16856])).
% 11.23/4.09  tff(c_16860, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 11.23/4.09  tff(c_16859, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 11.23/4.09  tff(c_16861, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_16859])).
% 11.23/4.09  tff(c_16868, plain, (![B_658, A_659]: (r1_tarski(B_658, k2_pre_topc(A_659, B_658)) | ~m1_subset_1(B_658, k1_zfmisc_1(u1_struct_0(A_659))) | ~l1_pre_topc(A_659))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.23/4.09  tff(c_16875, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_16868])).
% 11.23/4.09  tff(c_16882, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16875])).
% 11.23/4.09  tff(c_16967, plain, (![A_674, B_675]: (k1_tops_1(A_674, k2_pre_topc(A_674, B_675))=B_675 | ~v6_tops_1(B_675, A_674) | ~m1_subset_1(B_675, k1_zfmisc_1(u1_struct_0(A_674))) | ~l1_pre_topc(A_674))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.23/4.09  tff(c_16978, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_16967])).
% 11.23/4.09  tff(c_16987, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12335, c_16978])).
% 11.23/4.09  tff(c_20, plain, (![B_15, A_13]: (v5_tops_1(B_15, A_13) | k2_pre_topc(A_13, k1_tops_1(A_13, B_15))!=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.23/4.09  tff(c_17013, plain, (v5_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16987, c_20])).
% 11.23/4.09  tff(c_17021, plain, (v5_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_17013])).
% 11.23/4.09  tff(c_17035, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_17021])).
% 11.23/4.09  tff(c_17072, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_17035])).
% 11.23/4.09  tff(c_17076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_17072])).
% 11.23/4.09  tff(c_17078, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_17021])).
% 11.23/4.09  tff(c_17105, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17078, c_32])).
% 11.23/4.09  tff(c_17118, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16987, c_16987, c_17105])).
% 11.23/4.09  tff(c_17426, plain, (![B_705, A_706]: (v4_tops_1(B_705, A_706) | ~r1_tarski(B_705, k2_pre_topc(A_706, k1_tops_1(A_706, B_705))) | ~r1_tarski(k1_tops_1(A_706, k2_pre_topc(A_706, B_705)), B_705) | ~m1_subset_1(B_705, k1_zfmisc_1(u1_struct_0(A_706))) | ~l1_pre_topc(A_706))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.23/4.09  tff(c_17432, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16987, c_17426])).
% 11.23/4.09  tff(c_17438, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6, c_16882, c_17118, c_17432])).
% 11.23/4.09  tff(c_17440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16861, c_17438])).
% 11.23/4.09  tff(c_17442, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_16859])).
% 11.23/4.09  tff(c_12336, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 11.23/4.09  tff(c_54, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.23/4.09  tff(c_17446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16860, c_17442, c_12336, c_54])).
% 11.23/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.23/4.09  
% 11.23/4.09  Inference rules
% 11.23/4.09  ----------------------
% 11.23/4.09  #Ref     : 0
% 11.23/4.09  #Sup     : 3941
% 11.23/4.09  #Fact    : 0
% 11.23/4.09  #Define  : 0
% 11.23/4.09  #Split   : 170
% 11.23/4.09  #Chain   : 0
% 11.23/4.09  #Close   : 0
% 11.23/4.09  
% 11.23/4.09  Ordering : KBO
% 11.23/4.09  
% 11.23/4.09  Simplification rules
% 11.23/4.09  ----------------------
% 11.23/4.09  #Subsume      : 491
% 11.23/4.09  #Demod        : 4810
% 11.23/4.09  #Tautology    : 1268
% 11.23/4.09  #SimpNegUnit  : 153
% 11.23/4.09  #BackRed      : 30
% 11.23/4.09  
% 11.23/4.09  #Partial instantiations: 0
% 11.23/4.09  #Strategies tried      : 1
% 11.23/4.09  
% 11.23/4.09  Timing (in seconds)
% 11.23/4.09  ----------------------
% 11.23/4.10  Preprocessing        : 0.33
% 11.23/4.10  Parsing              : 0.18
% 11.23/4.10  CNF conversion       : 0.03
% 11.23/4.10  Main loop            : 2.97
% 11.23/4.10  Inferencing          : 0.86
% 11.23/4.10  Reduction            : 1.14
% 11.23/4.10  Demodulation         : 0.84
% 11.23/4.10  BG Simplification    : 0.12
% 11.23/4.10  Subsumption          : 0.67
% 11.23/4.10  Abstraction          : 0.15
% 11.23/4.10  MUC search           : 0.00
% 11.23/4.10  Cooper               : 0.00
% 11.23/4.10  Total                : 3.36
% 11.23/4.10  Index Insertion      : 0.00
% 11.23/4.10  Index Deletion       : 0.00
% 11.23/4.10  Index Matching       : 0.00
% 11.23/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
