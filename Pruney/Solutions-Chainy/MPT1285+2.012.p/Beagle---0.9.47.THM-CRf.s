%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:25 EST 2020

% Result     : Theorem 12.54s
% Output     : CNFRefutation 12.75s
% Verified   : 
% Statistics : Number of formulae       :  305 (1200 expanded)
%              Number of leaves         :   30 ( 410 expanded)
%              Depth                    :   15
%              Number of atoms          :  660 (4680 expanded)
%              Number of equality atoms :   70 ( 230 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_150,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_101,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_115,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tops_1)).

tff(c_54,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_61,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_94,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_62,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_380,plain,(
    ! [A_89,B_90] :
      ( k1_tops_1(A_89,k2_pre_topc(A_89,B_90)) = B_90
      | ~ v6_tops_1(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_389,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_380])).

tff(c_397,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62,c_389])).

tff(c_256,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k2_pre_topc(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_263,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k2_pre_topc(A_78,B_79),u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_256,c_10])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_171,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tops_1(A_74,B_75),B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_179,plain,(
    ! [A_74,A_6] :
      ( r1_tarski(k1_tops_1(A_74,A_6),A_6)
      | ~ l1_pre_topc(A_74)
      | ~ r1_tarski(A_6,u1_struct_0(A_74)) ) ),
    inference(resolution,[status(thm)],[c_12,c_171])).

tff(c_401,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_179])).

tff(c_405,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_401])).

tff(c_407,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_410,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_263,c_407])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_410])).

tff(c_419,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_329,plain,(
    ! [A_85,B_86] :
      ( k1_tops_1(A_85,k1_tops_1(A_85,B_86)) = k1_tops_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_854,plain,(
    ! [A_107,A_108] :
      ( k1_tops_1(A_107,k1_tops_1(A_107,A_108)) = k1_tops_1(A_107,A_108)
      | ~ l1_pre_topc(A_107)
      | ~ r1_tarski(A_108,u1_struct_0(A_107)) ) ),
    inference(resolution,[status(thm)],[c_12,c_329])).

tff(c_859,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_419,c_854])).

tff(c_883,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_397,c_397,c_859])).

tff(c_178,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_171])).

tff(c_185,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_178])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_254,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_915,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_254])).

tff(c_922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_915])).

tff(c_923,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_30,plain,(
    ! [C_33,A_21,D_35,B_29] :
      ( v3_pre_topc(C_33,A_21)
      | k1_tops_1(A_21,C_33) != C_33
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0(B_29)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2743,plain,(
    ! [D_193,B_194] :
      ( ~ m1_subset_1(D_193,k1_zfmisc_1(u1_struct_0(B_194)))
      | ~ l1_pre_topc(B_194) ) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2750,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_2743])).

tff(c_2758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2750])).

tff(c_2760,plain,(
    ! [C_195,A_196] :
      ( v3_pre_topc(C_195,A_196)
      | k1_tops_1(A_196,C_195) != C_195
      | ~ m1_subset_1(C_195,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2773,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2760])).

tff(c_2782,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_923,c_2773])).

tff(c_2784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2782])).

tff(c_2786,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2788,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2786,c_50])).

tff(c_2789,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2788])).

tff(c_3660,plain,(
    ! [A_248,B_249] :
      ( m1_subset_1(k2_pre_topc(A_248,B_249),k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3873,plain,(
    ! [A_264,B_265] :
      ( r1_tarski(k2_pre_topc(A_264,B_265),u1_struct_0(A_264))
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(resolution,[status(thm)],[c_3660,c_10])).

tff(c_3821,plain,(
    ! [A_261,B_262] :
      ( k1_tops_1(A_261,k2_pre_topc(A_261,B_262)) = B_262
      | ~ v6_tops_1(B_262,A_261)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3830,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3821])).

tff(c_3838,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62,c_3830])).

tff(c_2814,plain,(
    ! [A_202,B_203] :
      ( r1_tarski(k1_tops_1(A_202,B_203),B_203)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2822,plain,(
    ! [A_202,A_6] :
      ( r1_tarski(k1_tops_1(A_202,A_6),A_6)
      | ~ l1_pre_topc(A_202)
      | ~ r1_tarski(A_6,u1_struct_0(A_202)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2814])).

tff(c_3842,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3838,c_2822])).

tff(c_3846,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3842])).

tff(c_3848,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3846])).

tff(c_3876,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3873,c_3848])).

tff(c_3888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_3876])).

tff(c_3889,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3846])).

tff(c_3017,plain,(
    ! [A_218,B_219] :
      ( k1_tops_1(A_218,k2_pre_topc(A_218,B_219)) = B_219
      | ~ v6_tops_1(B_219,A_218)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3026,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3017])).

tff(c_3034,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62,c_3026])).

tff(c_2873,plain,(
    ! [A_207,B_208] :
      ( m1_subset_1(k2_pre_topc(A_207,B_208),k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3120,plain,(
    ! [A_225,B_226] :
      ( r1_tarski(k2_pre_topc(A_225,B_226),u1_struct_0(A_225))
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225) ) ),
    inference(resolution,[status(thm)],[c_2873,c_10])).

tff(c_3039,plain,(
    ! [A_220,A_221] :
      ( r1_tarski(k1_tops_1(A_220,A_221),A_221)
      | ~ l1_pre_topc(A_220)
      | ~ r1_tarski(A_221,u1_struct_0(A_220)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2814])).

tff(c_3066,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3034,c_3039])).

tff(c_3082,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3066])).

tff(c_3087,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3082])).

tff(c_3123,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3120,c_3087])).

tff(c_3135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_3123])).

tff(c_3137,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3082])).

tff(c_2966,plain,(
    ! [A_214,B_215] :
      ( k1_tops_1(A_214,k1_tops_1(A_214,B_215)) = k1_tops_1(A_214,B_215)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3579,plain,(
    ! [A_246,A_247] :
      ( k1_tops_1(A_246,k1_tops_1(A_246,A_247)) = k1_tops_1(A_246,A_247)
      | ~ l1_pre_topc(A_246)
      | ~ r1_tarski(A_247,u1_struct_0(A_246)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2966])).

tff(c_3586,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3137,c_3579])).

tff(c_3609,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3034,c_3034,c_3586])).

tff(c_2821,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2814])).

tff(c_2828,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2821])).

tff(c_2840,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2828,c_2])).

tff(c_2855,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2840])).

tff(c_3641,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3609,c_2855])).

tff(c_3648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3641])).

tff(c_3649,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2840])).

tff(c_5660,plain,(
    ! [B_343,A_344] :
      ( v4_tops_1(B_343,A_344)
      | ~ r1_tarski(B_343,k2_pre_topc(A_344,k1_tops_1(A_344,B_343)))
      | ~ r1_tarski(k1_tops_1(A_344,k2_pre_topc(A_344,B_343)),B_343)
      | ~ m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5699,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3838,c_5660])).

tff(c_5722,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_6,c_3889,c_3649,c_5699])).

tff(c_5724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2789,c_5722])).

tff(c_5725,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2788])).

tff(c_5771,plain,(
    ! [A_352,B_353] :
      ( r1_tarski(k1_tops_1(A_352,B_353),B_353)
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0(A_352)))
      | ~ l1_pre_topc(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5776,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_5771])).

tff(c_5782,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5776])).

tff(c_5794,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_5782,c_2])).

tff(c_6273,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5794])).

tff(c_5726,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2788])).

tff(c_2785,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5728,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5726,c_2785])).

tff(c_7456,plain,(
    ! [B_425,A_426,C_427] :
      ( r1_tarski(B_425,k1_tops_1(A_426,C_427))
      | ~ r1_tarski(B_425,C_427)
      | ~ v3_pre_topc(B_425,A_426)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_pre_topc(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7465,plain,(
    ! [B_425] :
      ( r1_tarski(B_425,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_425,'#skF_4')
      | ~ v3_pre_topc(B_425,'#skF_2')
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_7456])).

tff(c_7497,plain,(
    ! [B_429] :
      ( r1_tarski(B_429,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_429,'#skF_4')
      | ~ v3_pre_topc(B_429,'#skF_2')
      | ~ m1_subset_1(B_429,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_7465])).

tff(c_7511,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_7497])).

tff(c_7519,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5728,c_6,c_7511])).

tff(c_7521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6273,c_7519])).

tff(c_7522,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5794])).

tff(c_7901,plain,(
    ! [B_453,A_454] :
      ( r1_tarski(B_453,k2_pre_topc(A_454,k1_tops_1(A_454,B_453)))
      | ~ v4_tops_1(B_453,A_454)
      | ~ m1_subset_1(B_453,k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ l1_pre_topc(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7929,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7522,c_7901])).

tff(c_7944,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_5725,c_7929])).

tff(c_20,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k1_tops_1(A_10,k2_pre_topc(A_10,B_12)),B_12)
      | ~ v4_tops_1(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_65,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_5729,plain,(
    ! [A_345,C_346,B_347] :
      ( r1_tarski(A_345,C_346)
      | ~ r1_tarski(B_347,C_346)
      | ~ r1_tarski(A_345,B_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5737,plain,(
    ! [A_345] :
      ( r1_tarski(A_345,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_345,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_5729])).

tff(c_8422,plain,(
    ! [A_471,B_472] :
      ( k2_pre_topc(A_471,k1_tops_1(A_471,k2_pre_topc(A_471,B_472))) = k2_pre_topc(A_471,B_472)
      | ~ v3_pre_topc(B_472,A_471)
      | ~ m1_subset_1(B_472,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ l1_pre_topc(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8429,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_8422])).

tff(c_8436,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5728,c_8429])).

tff(c_6264,plain,(
    ! [A_379,B_380] :
      ( m1_subset_1(k2_pre_topc(A_379,B_380),k1_zfmisc_1(u1_struct_0(A_379)))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_379)))
      | ~ l1_pre_topc(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6271,plain,(
    ! [A_379,B_380] :
      ( r1_tarski(k2_pre_topc(A_379,B_380),u1_struct_0(A_379))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_379)))
      | ~ l1_pre_topc(A_379) ) ),
    inference(resolution,[status(thm)],[c_6264,c_10])).

tff(c_8454,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8436,c_6271])).

tff(c_8472,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8454])).

tff(c_8586,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_8472])).

tff(c_8595,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_8586])).

tff(c_8604,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5737,c_8595])).

tff(c_8610,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_8604])).

tff(c_8616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_5725,c_8610])).

tff(c_8617,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_8472])).

tff(c_9136,plain,(
    ! [B_493,A_494,C_495] :
      ( r1_tarski(B_493,k1_tops_1(A_494,C_495))
      | ~ r1_tarski(B_493,C_495)
      | ~ v3_pre_topc(B_493,A_494)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(u1_struct_0(A_494)))
      | ~ m1_subset_1(B_493,k1_zfmisc_1(u1_struct_0(A_494)))
      | ~ l1_pre_topc(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_13101,plain,(
    ! [B_594,A_595,A_596] :
      ( r1_tarski(B_594,k1_tops_1(A_595,A_596))
      | ~ r1_tarski(B_594,A_596)
      | ~ v3_pre_topc(B_594,A_595)
      | ~ m1_subset_1(B_594,k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ l1_pre_topc(A_595)
      | ~ r1_tarski(A_596,u1_struct_0(A_595)) ) ),
    inference(resolution,[status(thm)],[c_12,c_9136])).

tff(c_13112,plain,(
    ! [A_596] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',A_596))
      | ~ r1_tarski('#skF_4',A_596)
      | ~ v3_pre_topc('#skF_4','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_596,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_38,c_13101])).

tff(c_13129,plain,(
    ! [A_597] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',A_597))
      | ~ r1_tarski('#skF_4',A_597)
      | ~ r1_tarski(A_597,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5728,c_13112])).

tff(c_13146,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8617,c_13129])).

tff(c_13175,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7944,c_13146])).

tff(c_8074,plain,(
    ! [A_458,B_459] :
      ( r1_tarski(k1_tops_1(A_458,k2_pre_topc(A_458,B_459)),B_459)
      | ~ v4_tops_1(B_459,A_458)
      | ~ m1_subset_1(B_459,k1_zfmisc_1(u1_struct_0(A_458)))
      | ~ l1_pre_topc(A_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14573,plain,(
    ! [A_614,B_615] :
      ( k1_tops_1(A_614,k2_pre_topc(A_614,B_615)) = B_615
      | ~ r1_tarski(B_615,k1_tops_1(A_614,k2_pre_topc(A_614,B_615)))
      | ~ v4_tops_1(B_615,A_614)
      | ~ m1_subset_1(B_615,k1_zfmisc_1(u1_struct_0(A_614)))
      | ~ l1_pre_topc(A_614) ) ),
    inference(resolution,[status(thm)],[c_8074,c_2])).

tff(c_14588,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_13175,c_14573])).

tff(c_14630,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_5725,c_14588])).

tff(c_8618,plain,(
    m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_8472])).

tff(c_22,plain,(
    ! [B_15,A_13] :
      ( v6_tops_1(B_15,A_13)
      | k1_tops_1(A_13,k2_pre_topc(A_13,B_15)) != B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8451,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8436,c_22])).

tff(c_8470,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8451])).

tff(c_9094,plain,(
    v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8618,c_8470])).

tff(c_14655,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14630,c_9094])).

tff(c_14665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_14655])).

tff(c_14667,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_14668,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_14667,c_56])).

tff(c_14724,plain,(
    ! [A_627,B_628] :
      ( r1_tarski(k1_tops_1(A_627,B_628),B_628)
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0(A_627)))
      | ~ l1_pre_topc(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14729,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_14724])).

tff(c_14735,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14729])).

tff(c_14744,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_14735,c_2])).

tff(c_14766,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14744])).

tff(c_14666,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16347,plain,(
    ! [B_699,A_700,C_701] :
      ( r1_tarski(B_699,k1_tops_1(A_700,C_701))
      | ~ r1_tarski(B_699,C_701)
      | ~ v3_pre_topc(B_699,A_700)
      | ~ m1_subset_1(C_701,k1_zfmisc_1(u1_struct_0(A_700)))
      | ~ m1_subset_1(B_699,k1_zfmisc_1(u1_struct_0(A_700)))
      | ~ l1_pre_topc(A_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_16358,plain,(
    ! [B_699] :
      ( r1_tarski(B_699,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_699,'#skF_4')
      | ~ v3_pre_topc(B_699,'#skF_2')
      | ~ m1_subset_1(B_699,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_16347])).

tff(c_16485,plain,(
    ! [B_705] :
      ( r1_tarski(B_705,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_705,'#skF_4')
      | ~ v3_pre_topc(B_705,'#skF_2')
      | ~ m1_subset_1(B_705,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16358])).

tff(c_16502,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_16485])).

tff(c_16511,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_6,c_16502])).

tff(c_16513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14766,c_16511])).

tff(c_16514,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14744])).

tff(c_17295,plain,(
    ! [B_752,A_753] :
      ( r1_tarski(B_752,k2_pre_topc(A_753,k1_tops_1(A_753,B_752)))
      | ~ v4_tops_1(B_752,A_753)
      | ~ m1_subset_1(B_752,k1_zfmisc_1(u1_struct_0(A_753)))
      | ~ l1_pre_topc(A_753) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_17337,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16514,c_17295])).

tff(c_17357,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_14668,c_17337])).

tff(c_16572,plain,(
    ! [A_709,B_710] :
      ( m1_subset_1(k2_pre_topc(A_709,B_710),k1_zfmisc_1(u1_struct_0(A_709)))
      | ~ m1_subset_1(B_710,k1_zfmisc_1(u1_struct_0(A_709)))
      | ~ l1_pre_topc(A_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_18,B_20] :
      ( r1_tarski(k1_tops_1(A_18,B_20),B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16578,plain,(
    ! [A_709,B_710] :
      ( r1_tarski(k1_tops_1(A_709,k2_pre_topc(A_709,B_710)),k2_pre_topc(A_709,B_710))
      | ~ m1_subset_1(B_710,k1_zfmisc_1(u1_struct_0(A_709)))
      | ~ l1_pre_topc(A_709) ) ),
    inference(resolution,[status(thm)],[c_16572,c_28])).

tff(c_16685,plain,(
    ! [A_719,B_720] :
      ( r1_tarski(k2_pre_topc(A_719,B_720),u1_struct_0(A_719))
      | ~ m1_subset_1(B_720,k1_zfmisc_1(u1_struct_0(A_719)))
      | ~ l1_pre_topc(A_719) ) ),
    inference(resolution,[status(thm)],[c_16572,c_10])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_17250,plain,(
    ! [A_747,A_748,B_749] :
      ( r1_tarski(A_747,u1_struct_0(A_748))
      | ~ r1_tarski(A_747,k2_pre_topc(A_748,B_749))
      | ~ m1_subset_1(B_749,k1_zfmisc_1(u1_struct_0(A_748)))
      | ~ l1_pre_topc(A_748) ) ),
    inference(resolution,[status(thm)],[c_16685,c_8])).

tff(c_17259,plain,(
    ! [A_709,B_710] :
      ( r1_tarski(k1_tops_1(A_709,k2_pre_topc(A_709,B_710)),u1_struct_0(A_709))
      | ~ m1_subset_1(B_710,k1_zfmisc_1(u1_struct_0(A_709)))
      | ~ l1_pre_topc(A_709) ) ),
    inference(resolution,[status(thm)],[c_16578,c_17250])).

tff(c_17785,plain,(
    ! [A_769,B_770] :
      ( k2_pre_topc(A_769,k1_tops_1(A_769,k2_pre_topc(A_769,B_770))) = k2_pre_topc(A_769,B_770)
      | ~ v3_pre_topc(B_770,A_769)
      | ~ m1_subset_1(B_770,k1_zfmisc_1(u1_struct_0(A_769)))
      | ~ l1_pre_topc(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_17792,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_17785])).

tff(c_17799,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14666,c_17792])).

tff(c_16579,plain,(
    ! [A_709,B_710] :
      ( r1_tarski(k2_pre_topc(A_709,B_710),u1_struct_0(A_709))
      | ~ m1_subset_1(B_710,k1_zfmisc_1(u1_struct_0(A_709)))
      | ~ l1_pre_topc(A_709) ) ),
    inference(resolution,[status(thm)],[c_16572,c_10])).

tff(c_17834,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17799,c_16579])).

tff(c_17862,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_17834])).

tff(c_17869,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_17862])).

tff(c_17878,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_17869])).

tff(c_17881,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_17259,c_17878])).

tff(c_17894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_17881])).

tff(c_17895,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17862])).

tff(c_18184,plain,(
    ! [B_777,A_778,C_779] :
      ( r1_tarski(B_777,k1_tops_1(A_778,C_779))
      | ~ r1_tarski(B_777,C_779)
      | ~ v3_pre_topc(B_777,A_778)
      | ~ m1_subset_1(C_779,k1_zfmisc_1(u1_struct_0(A_778)))
      | ~ m1_subset_1(B_777,k1_zfmisc_1(u1_struct_0(A_778)))
      | ~ l1_pre_topc(A_778) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_21214,plain,(
    ! [B_858,A_859,A_860] :
      ( r1_tarski(B_858,k1_tops_1(A_859,A_860))
      | ~ r1_tarski(B_858,A_860)
      | ~ v3_pre_topc(B_858,A_859)
      | ~ m1_subset_1(B_858,k1_zfmisc_1(u1_struct_0(A_859)))
      | ~ l1_pre_topc(A_859)
      | ~ r1_tarski(A_860,u1_struct_0(A_859)) ) ),
    inference(resolution,[status(thm)],[c_12,c_18184])).

tff(c_21225,plain,(
    ! [A_860] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',A_860))
      | ~ r1_tarski('#skF_4',A_860)
      | ~ v3_pre_topc('#skF_4','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_860,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_38,c_21214])).

tff(c_21242,plain,(
    ! [A_861] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',A_861))
      | ~ r1_tarski('#skF_4',A_861)
      | ~ r1_tarski(A_861,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14666,c_21225])).

tff(c_21250,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_17895,c_21242])).

tff(c_21280,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17357,c_21250])).

tff(c_21401,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_21280,c_2])).

tff(c_21964,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_21401])).

tff(c_21970,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_21964])).

tff(c_21979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_14668,c_21970])).

tff(c_21980,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21401])).

tff(c_17896,plain,(
    m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_17862])).

tff(c_17828,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17799,c_22])).

tff(c_17859,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_17828])).

tff(c_18069,plain,(
    v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17896,c_17859])).

tff(c_22020,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21980,c_18069])).

tff(c_22029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_22020])).

tff(c_22031,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_22064,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22031,c_48])).

tff(c_22065,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22064])).

tff(c_22030,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_22710,plain,(
    ! [A_921,B_922] :
      ( k1_tops_1(A_921,k2_pre_topc(A_921,B_922)) = B_922
      | ~ v6_tops_1(B_922,A_921)
      | ~ m1_subset_1(B_922,k1_zfmisc_1(u1_struct_0(A_921)))
      | ~ l1_pre_topc(A_921) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22719,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_22710])).

tff(c_22727,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22030,c_22719])).

tff(c_22243,plain,(
    ! [A_893,B_894] :
      ( m1_subset_1(k2_pre_topc(A_893,B_894),k1_zfmisc_1(u1_struct_0(A_893)))
      | ~ m1_subset_1(B_894,k1_zfmisc_1(u1_struct_0(A_893)))
      | ~ l1_pre_topc(A_893) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22250,plain,(
    ! [A_893,B_894] :
      ( r1_tarski(k2_pre_topc(A_893,B_894),u1_struct_0(A_893))
      | ~ m1_subset_1(B_894,k1_zfmisc_1(u1_struct_0(A_893)))
      | ~ l1_pre_topc(A_893) ) ),
    inference(resolution,[status(thm)],[c_22243,c_10])).

tff(c_22158,plain,(
    ! [A_889,B_890] :
      ( r1_tarski(k1_tops_1(A_889,B_890),B_890)
      | ~ m1_subset_1(B_890,k1_zfmisc_1(u1_struct_0(A_889)))
      | ~ l1_pre_topc(A_889) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22166,plain,(
    ! [A_889,A_6] :
      ( r1_tarski(k1_tops_1(A_889,A_6),A_6)
      | ~ l1_pre_topc(A_889)
      | ~ r1_tarski(A_6,u1_struct_0(A_889)) ) ),
    inference(resolution,[status(thm)],[c_12,c_22158])).

tff(c_22784,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22727,c_22166])).

tff(c_22800,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22784])).

tff(c_22804,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_22800])).

tff(c_22807,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22250,c_22804])).

tff(c_22814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_22807])).

tff(c_22816,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_22800])).

tff(c_22300,plain,(
    ! [A_899,B_900] :
      ( k1_tops_1(A_899,k1_tops_1(A_899,B_900)) = k1_tops_1(A_899,B_900)
      | ~ m1_subset_1(B_900,k1_zfmisc_1(u1_struct_0(A_899)))
      | ~ l1_pre_topc(A_899) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22311,plain,(
    ! [A_899,A_6] :
      ( k1_tops_1(A_899,k1_tops_1(A_899,A_6)) = k1_tops_1(A_899,A_6)
      | ~ l1_pre_topc(A_899)
      | ~ r1_tarski(A_6,u1_struct_0(A_899)) ) ),
    inference(resolution,[status(thm)],[c_12,c_22300])).

tff(c_22882,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22816,c_22311])).

tff(c_22893,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22727,c_22727,c_22882])).

tff(c_22165,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_22158])).

tff(c_22172,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22165])).

tff(c_22200,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22172,c_2])).

tff(c_22241,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_22200])).

tff(c_22903,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22893,c_22241])).

tff(c_22909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22903])).

tff(c_22910,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22200])).

tff(c_24659,plain,(
    ! [D_1000,B_1001] :
      ( ~ m1_subset_1(D_1000,k1_zfmisc_1(u1_struct_0(B_1001)))
      | ~ l1_pre_topc(B_1001) ) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_24666,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_24659])).

tff(c_24674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_24666])).

tff(c_24755,plain,(
    ! [C_1004,A_1005] :
      ( v3_pre_topc(C_1004,A_1005)
      | k1_tops_1(A_1005,C_1004) != C_1004
      | ~ m1_subset_1(C_1004,k1_zfmisc_1(u1_struct_0(A_1005)))
      | ~ l1_pre_topc(A_1005)
      | ~ v2_pre_topc(A_1005) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_24768,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_24755])).

tff(c_24776,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_22910,c_24768])).

tff(c_24778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22065,c_24776])).

tff(c_24779,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22064])).

tff(c_26084,plain,(
    ! [A_1078,B_1079] :
      ( m1_subset_1(k2_pre_topc(A_1078,B_1079),k1_zfmisc_1(u1_struct_0(A_1078)))
      | ~ m1_subset_1(B_1079,k1_zfmisc_1(u1_struct_0(A_1078)))
      | ~ l1_pre_topc(A_1078) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26091,plain,(
    ! [A_1078,B_1079] :
      ( r1_tarski(k2_pre_topc(A_1078,B_1079),u1_struct_0(A_1078))
      | ~ m1_subset_1(B_1079,k1_zfmisc_1(u1_struct_0(A_1078)))
      | ~ l1_pre_topc(A_1078) ) ),
    inference(resolution,[status(thm)],[c_26084,c_10])).

tff(c_26999,plain,(
    ! [A_1132,B_1133] :
      ( k1_tops_1(A_1132,k2_pre_topc(A_1132,B_1133)) = B_1133
      | ~ v6_tops_1(B_1133,A_1132)
      | ~ m1_subset_1(B_1133,k1_zfmisc_1(u1_struct_0(A_1132)))
      | ~ l1_pre_topc(A_1132) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_27008,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_26999])).

tff(c_27016,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22030,c_27008])).

tff(c_24827,plain,(
    ! [A_1013,B_1014] :
      ( r1_tarski(k1_tops_1(A_1013,B_1014),B_1014)
      | ~ m1_subset_1(B_1014,k1_zfmisc_1(u1_struct_0(A_1013)))
      | ~ l1_pre_topc(A_1013) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24835,plain,(
    ! [A_1013,A_6] :
      ( r1_tarski(k1_tops_1(A_1013,A_6),A_6)
      | ~ l1_pre_topc(A_1013)
      | ~ r1_tarski(A_6,u1_struct_0(A_1013)) ) ),
    inference(resolution,[status(thm)],[c_12,c_24827])).

tff(c_27073,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27016,c_24835])).

tff(c_27089,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_27073])).

tff(c_27273,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_27089])).

tff(c_27276,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26091,c_27273])).

tff(c_27283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_27276])).

tff(c_27284,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_27089])).

tff(c_25861,plain,(
    ! [A_1074,B_1075] :
      ( k1_tops_1(A_1074,k2_pre_topc(A_1074,B_1075)) = B_1075
      | ~ v6_tops_1(B_1075,A_1074)
      | ~ m1_subset_1(B_1075,k1_zfmisc_1(u1_struct_0(A_1074)))
      | ~ l1_pre_topc(A_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_25870,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_25861])).

tff(c_25878,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22030,c_25870])).

tff(c_25433,plain,(
    ! [A_1046,B_1047] :
      ( m1_subset_1(k2_pre_topc(A_1046,B_1047),k1_zfmisc_1(u1_struct_0(A_1046)))
      | ~ m1_subset_1(B_1047,k1_zfmisc_1(u1_struct_0(A_1046)))
      | ~ l1_pre_topc(A_1046) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_25440,plain,(
    ! [A_1046,B_1047] :
      ( r1_tarski(k2_pre_topc(A_1046,B_1047),u1_struct_0(A_1046))
      | ~ m1_subset_1(B_1047,k1_zfmisc_1(u1_struct_0(A_1046)))
      | ~ l1_pre_topc(A_1046) ) ),
    inference(resolution,[status(thm)],[c_25433,c_10])).

tff(c_25935,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25878,c_24835])).

tff(c_25951,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_25935])).

tff(c_26011,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_25951])).

tff(c_26018,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_25440,c_26011])).

tff(c_26028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_26018])).

tff(c_26030,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_25951])).

tff(c_25487,plain,(
    ! [A_1051,B_1052] :
      ( k1_tops_1(A_1051,k1_tops_1(A_1051,B_1052)) = k1_tops_1(A_1051,B_1052)
      | ~ m1_subset_1(B_1052,k1_zfmisc_1(u1_struct_0(A_1051)))
      | ~ l1_pre_topc(A_1051) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_25498,plain,(
    ! [A_1051,A_6] :
      ( k1_tops_1(A_1051,k1_tops_1(A_1051,A_6)) = k1_tops_1(A_1051,A_6)
      | ~ l1_pre_topc(A_1051)
      | ~ r1_tarski(A_6,u1_struct_0(A_1051)) ) ),
    inference(resolution,[status(thm)],[c_12,c_25487])).

tff(c_26045,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26030,c_25498])).

tff(c_26056,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_25878,c_25878,c_26045])).

tff(c_24834,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_24827])).

tff(c_24841,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_24834])).

tff(c_24861,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24841,c_2])).

tff(c_24886,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24861])).

tff(c_26066,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26056,c_24886])).

tff(c_26072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26066])).

tff(c_26073,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24861])).

tff(c_28354,plain,(
    ! [B_1184,A_1185] :
      ( v4_tops_1(B_1184,A_1185)
      | ~ r1_tarski(B_1184,k2_pre_topc(A_1185,k1_tops_1(A_1185,B_1184)))
      | ~ r1_tarski(k1_tops_1(A_1185,k2_pre_topc(A_1185,B_1184)),B_1184)
      | ~ m1_subset_1(B_1184,k1_zfmisc_1(u1_struct_0(A_1185)))
      | ~ l1_pre_topc(A_1185) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28381,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_27016,c_28354])).

tff(c_28412,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_6,c_27284,c_26073,c_28381])).

tff(c_28414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24779,c_28412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:46:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.54/4.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/4.83  
% 12.73/4.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/4.83  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.73/4.83  
% 12.73/4.83  %Foreground sorts:
% 12.73/4.83  
% 12.73/4.83  
% 12.73/4.83  %Background operators:
% 12.73/4.83  
% 12.73/4.83  
% 12.73/4.83  %Foreground operators:
% 12.73/4.83  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.73/4.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.73/4.83  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 12.73/4.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.73/4.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.73/4.83  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 12.73/4.83  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 12.73/4.83  tff('#skF_2', type, '#skF_2': $i).
% 12.73/4.83  tff('#skF_3', type, '#skF_3': $i).
% 12.73/4.83  tff('#skF_1', type, '#skF_1': $i).
% 12.73/4.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.73/4.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.73/4.83  tff('#skF_4', type, '#skF_4': $i).
% 12.73/4.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.73/4.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.73/4.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.73/4.83  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.73/4.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.73/4.83  
% 12.75/4.86  tff(f_150, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 12.75/4.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.75/4.86  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 12.75/4.86  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 12.75/4.86  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.75/4.86  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 12.75/4.86  tff(f_73, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 12.75/4.86  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 12.75/4.86  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 12.75/4.86  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 12.75/4.86  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 12.75/4.86  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tops_1)).
% 12.75/4.86  tff(c_54, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_61, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 12.75/4.86  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_52, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_94, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 12.75/4.86  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.75/4.86  tff(c_58, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_62, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 12.75/4.86  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_380, plain, (![A_89, B_90]: (k1_tops_1(A_89, k2_pre_topc(A_89, B_90))=B_90 | ~v6_tops_1(B_90, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.75/4.86  tff(c_389, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_380])).
% 12.75/4.86  tff(c_397, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_62, c_389])).
% 12.75/4.86  tff(c_256, plain, (![A_78, B_79]: (m1_subset_1(k2_pre_topc(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/4.86  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.75/4.86  tff(c_263, plain, (![A_78, B_79]: (r1_tarski(k2_pre_topc(A_78, B_79), u1_struct_0(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_256, c_10])).
% 12.75/4.86  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.75/4.86  tff(c_171, plain, (![A_74, B_75]: (r1_tarski(k1_tops_1(A_74, B_75), B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.75/4.86  tff(c_179, plain, (![A_74, A_6]: (r1_tarski(k1_tops_1(A_74, A_6), A_6) | ~l1_pre_topc(A_74) | ~r1_tarski(A_6, u1_struct_0(A_74)))), inference(resolution, [status(thm)], [c_12, c_171])).
% 12.75/4.86  tff(c_401, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_397, c_179])).
% 12.75/4.86  tff(c_405, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_401])).
% 12.75/4.86  tff(c_407, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_405])).
% 12.75/4.86  tff(c_410, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_263, c_407])).
% 12.75/4.86  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_410])).
% 12.75/4.86  tff(c_419, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_405])).
% 12.75/4.86  tff(c_329, plain, (![A_85, B_86]: (k1_tops_1(A_85, k1_tops_1(A_85, B_86))=k1_tops_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.75/4.86  tff(c_854, plain, (![A_107, A_108]: (k1_tops_1(A_107, k1_tops_1(A_107, A_108))=k1_tops_1(A_107, A_108) | ~l1_pre_topc(A_107) | ~r1_tarski(A_108, u1_struct_0(A_107)))), inference(resolution, [status(thm)], [c_12, c_329])).
% 12.75/4.86  tff(c_859, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_419, c_854])).
% 12.75/4.86  tff(c_883, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_397, c_397, c_859])).
% 12.75/4.86  tff(c_178, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_171])).
% 12.75/4.86  tff(c_185, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_178])).
% 12.75/4.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.75/4.86  tff(c_213, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_185, c_2])).
% 12.75/4.86  tff(c_254, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_213])).
% 12.75/4.86  tff(c_915, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_254])).
% 12.75/4.86  tff(c_922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_915])).
% 12.75/4.86  tff(c_923, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_213])).
% 12.75/4.86  tff(c_30, plain, (![C_33, A_21, D_35, B_29]: (v3_pre_topc(C_33, A_21) | k1_tops_1(A_21, C_33)!=C_33 | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0(B_29))) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.75/4.86  tff(c_2743, plain, (![D_193, B_194]: (~m1_subset_1(D_193, k1_zfmisc_1(u1_struct_0(B_194))) | ~l1_pre_topc(B_194))), inference(splitLeft, [status(thm)], [c_30])).
% 12.75/4.86  tff(c_2750, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_2743])).
% 12.75/4.86  tff(c_2758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_2750])).
% 12.75/4.86  tff(c_2760, plain, (![C_195, A_196]: (v3_pre_topc(C_195, A_196) | k1_tops_1(A_196, C_195)!=C_195 | ~m1_subset_1(C_195, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196))), inference(splitRight, [status(thm)], [c_30])).
% 12.75/4.86  tff(c_2773, plain, (v3_pre_topc('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2760])).
% 12.75/4.86  tff(c_2782, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_923, c_2773])).
% 12.75/4.86  tff(c_2784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_2782])).
% 12.75/4.86  tff(c_2786, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 12.75/4.86  tff(c_50, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.86  tff(c_2788, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2786, c_50])).
% 12.75/4.86  tff(c_2789, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_2788])).
% 12.75/4.86  tff(c_3660, plain, (![A_248, B_249]: (m1_subset_1(k2_pre_topc(A_248, B_249), k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/4.86  tff(c_3873, plain, (![A_264, B_265]: (r1_tarski(k2_pre_topc(A_264, B_265), u1_struct_0(A_264)) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(resolution, [status(thm)], [c_3660, c_10])).
% 12.75/4.86  tff(c_3821, plain, (![A_261, B_262]: (k1_tops_1(A_261, k2_pre_topc(A_261, B_262))=B_262 | ~v6_tops_1(B_262, A_261) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.75/4.86  tff(c_3830, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3821])).
% 12.75/4.86  tff(c_3838, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_62, c_3830])).
% 12.75/4.86  tff(c_2814, plain, (![A_202, B_203]: (r1_tarski(k1_tops_1(A_202, B_203), B_203) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.75/4.86  tff(c_2822, plain, (![A_202, A_6]: (r1_tarski(k1_tops_1(A_202, A_6), A_6) | ~l1_pre_topc(A_202) | ~r1_tarski(A_6, u1_struct_0(A_202)))), inference(resolution, [status(thm)], [c_12, c_2814])).
% 12.75/4.86  tff(c_3842, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3838, c_2822])).
% 12.75/4.86  tff(c_3846, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3842])).
% 12.75/4.86  tff(c_3848, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_3846])).
% 12.75/4.86  tff(c_3876, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3873, c_3848])).
% 12.75/4.86  tff(c_3888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_3876])).
% 12.75/4.86  tff(c_3889, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_3846])).
% 12.75/4.86  tff(c_3017, plain, (![A_218, B_219]: (k1_tops_1(A_218, k2_pre_topc(A_218, B_219))=B_219 | ~v6_tops_1(B_219, A_218) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.75/4.86  tff(c_3026, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3017])).
% 12.75/4.86  tff(c_3034, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_62, c_3026])).
% 12.75/4.86  tff(c_2873, plain, (![A_207, B_208]: (m1_subset_1(k2_pre_topc(A_207, B_208), k1_zfmisc_1(u1_struct_0(A_207))) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/4.86  tff(c_3120, plain, (![A_225, B_226]: (r1_tarski(k2_pre_topc(A_225, B_226), u1_struct_0(A_225)) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225))), inference(resolution, [status(thm)], [c_2873, c_10])).
% 12.75/4.86  tff(c_3039, plain, (![A_220, A_221]: (r1_tarski(k1_tops_1(A_220, A_221), A_221) | ~l1_pre_topc(A_220) | ~r1_tarski(A_221, u1_struct_0(A_220)))), inference(resolution, [status(thm)], [c_12, c_2814])).
% 12.75/4.86  tff(c_3066, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3034, c_3039])).
% 12.75/4.86  tff(c_3082, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3066])).
% 12.75/4.86  tff(c_3087, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_3082])).
% 12.75/4.86  tff(c_3123, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3120, c_3087])).
% 12.75/4.86  tff(c_3135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_3123])).
% 12.75/4.86  tff(c_3137, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_3082])).
% 12.75/4.86  tff(c_2966, plain, (![A_214, B_215]: (k1_tops_1(A_214, k1_tops_1(A_214, B_215))=k1_tops_1(A_214, B_215) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.75/4.86  tff(c_3579, plain, (![A_246, A_247]: (k1_tops_1(A_246, k1_tops_1(A_246, A_247))=k1_tops_1(A_246, A_247) | ~l1_pre_topc(A_246) | ~r1_tarski(A_247, u1_struct_0(A_246)))), inference(resolution, [status(thm)], [c_12, c_2966])).
% 12.75/4.86  tff(c_3586, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3137, c_3579])).
% 12.75/4.86  tff(c_3609, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3034, c_3034, c_3586])).
% 12.75/4.86  tff(c_2821, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2814])).
% 12.75/4.86  tff(c_2828, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2821])).
% 12.75/4.86  tff(c_2840, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_2828, c_2])).
% 12.75/4.86  tff(c_2855, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2840])).
% 12.75/4.86  tff(c_3641, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3609, c_2855])).
% 12.75/4.86  tff(c_3648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3641])).
% 12.75/4.86  tff(c_3649, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2840])).
% 12.75/4.86  tff(c_5660, plain, (![B_343, A_344]: (v4_tops_1(B_343, A_344) | ~r1_tarski(B_343, k2_pre_topc(A_344, k1_tops_1(A_344, B_343))) | ~r1_tarski(k1_tops_1(A_344, k2_pre_topc(A_344, B_343)), B_343) | ~m1_subset_1(B_343, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.75/4.86  tff(c_5699, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3838, c_5660])).
% 12.75/4.86  tff(c_5722, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_6, c_3889, c_3649, c_5699])).
% 12.75/4.86  tff(c_5724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2789, c_5722])).
% 12.75/4.86  tff(c_5725, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_2788])).
% 12.75/4.86  tff(c_5771, plain, (![A_352, B_353]: (r1_tarski(k1_tops_1(A_352, B_353), B_353) | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0(A_352))) | ~l1_pre_topc(A_352))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.75/4.86  tff(c_5776, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_5771])).
% 12.75/4.86  tff(c_5782, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5776])).
% 12.75/4.86  tff(c_5794, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_5782, c_2])).
% 12.75/4.86  tff(c_6273, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_5794])).
% 12.75/4.86  tff(c_5726, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_2788])).
% 12.75/4.86  tff(c_2785, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 12.75/4.86  tff(c_5728, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5726, c_2785])).
% 12.75/4.86  tff(c_7456, plain, (![B_425, A_426, C_427]: (r1_tarski(B_425, k1_tops_1(A_426, C_427)) | ~r1_tarski(B_425, C_427) | ~v3_pre_topc(B_425, A_426) | ~m1_subset_1(C_427, k1_zfmisc_1(u1_struct_0(A_426))) | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_pre_topc(A_426))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.75/4.86  tff(c_7465, plain, (![B_425]: (r1_tarski(B_425, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_425, '#skF_4') | ~v3_pre_topc(B_425, '#skF_2') | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_7456])).
% 12.75/4.86  tff(c_7497, plain, (![B_429]: (r1_tarski(B_429, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_429, '#skF_4') | ~v3_pre_topc(B_429, '#skF_2') | ~m1_subset_1(B_429, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_7465])).
% 12.75/4.86  tff(c_7511, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_7497])).
% 12.75/4.86  tff(c_7519, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5728, c_6, c_7511])).
% 12.75/4.86  tff(c_7521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6273, c_7519])).
% 12.75/4.86  tff(c_7522, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_5794])).
% 12.75/4.86  tff(c_7901, plain, (![B_453, A_454]: (r1_tarski(B_453, k2_pre_topc(A_454, k1_tops_1(A_454, B_453))) | ~v4_tops_1(B_453, A_454) | ~m1_subset_1(B_453, k1_zfmisc_1(u1_struct_0(A_454))) | ~l1_pre_topc(A_454))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.75/4.86  tff(c_7929, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7522, c_7901])).
% 12.75/4.86  tff(c_7944, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_5725, c_7929])).
% 12.75/4.86  tff(c_20, plain, (![A_10, B_12]: (r1_tarski(k1_tops_1(A_10, k2_pre_topc(A_10, B_12)), B_12) | ~v4_tops_1(B_12, A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.75/4.86  tff(c_65, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.75/4.86  tff(c_72, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_65])).
% 12.75/4.86  tff(c_5729, plain, (![A_345, C_346, B_347]: (r1_tarski(A_345, C_346) | ~r1_tarski(B_347, C_346) | ~r1_tarski(A_345, B_347))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.75/4.86  tff(c_5737, plain, (![A_345]: (r1_tarski(A_345, u1_struct_0('#skF_2')) | ~r1_tarski(A_345, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_5729])).
% 12.75/4.86  tff(c_8422, plain, (![A_471, B_472]: (k2_pre_topc(A_471, k1_tops_1(A_471, k2_pre_topc(A_471, B_472)))=k2_pre_topc(A_471, B_472) | ~v3_pre_topc(B_472, A_471) | ~m1_subset_1(B_472, k1_zfmisc_1(u1_struct_0(A_471))) | ~l1_pre_topc(A_471))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.75/4.86  tff(c_8429, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_8422])).
% 12.75/4.86  tff(c_8436, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5728, c_8429])).
% 12.75/4.86  tff(c_6264, plain, (![A_379, B_380]: (m1_subset_1(k2_pre_topc(A_379, B_380), k1_zfmisc_1(u1_struct_0(A_379))) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_379))) | ~l1_pre_topc(A_379))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/4.86  tff(c_6271, plain, (![A_379, B_380]: (r1_tarski(k2_pre_topc(A_379, B_380), u1_struct_0(A_379)) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_379))) | ~l1_pre_topc(A_379))), inference(resolution, [status(thm)], [c_6264, c_10])).
% 12.75/4.86  tff(c_8454, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8436, c_6271])).
% 12.75/4.86  tff(c_8472, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8454])).
% 12.75/4.86  tff(c_8586, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_8472])).
% 12.75/4.87  tff(c_8595, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_8586])).
% 12.75/4.87  tff(c_8604, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(resolution, [status(thm)], [c_5737, c_8595])).
% 12.75/4.87  tff(c_8610, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_8604])).
% 12.75/4.87  tff(c_8616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_5725, c_8610])).
% 12.75/4.87  tff(c_8617, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_8472])).
% 12.75/4.87  tff(c_9136, plain, (![B_493, A_494, C_495]: (r1_tarski(B_493, k1_tops_1(A_494, C_495)) | ~r1_tarski(B_493, C_495) | ~v3_pre_topc(B_493, A_494) | ~m1_subset_1(C_495, k1_zfmisc_1(u1_struct_0(A_494))) | ~m1_subset_1(B_493, k1_zfmisc_1(u1_struct_0(A_494))) | ~l1_pre_topc(A_494))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.75/4.87  tff(c_13101, plain, (![B_594, A_595, A_596]: (r1_tarski(B_594, k1_tops_1(A_595, A_596)) | ~r1_tarski(B_594, A_596) | ~v3_pre_topc(B_594, A_595) | ~m1_subset_1(B_594, k1_zfmisc_1(u1_struct_0(A_595))) | ~l1_pre_topc(A_595) | ~r1_tarski(A_596, u1_struct_0(A_595)))), inference(resolution, [status(thm)], [c_12, c_9136])).
% 12.75/4.87  tff(c_13112, plain, (![A_596]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', A_596)) | ~r1_tarski('#skF_4', A_596) | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_596, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_38, c_13101])).
% 12.75/4.87  tff(c_13129, plain, (![A_597]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', A_597)) | ~r1_tarski('#skF_4', A_597) | ~r1_tarski(A_597, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5728, c_13112])).
% 12.75/4.87  tff(c_13146, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_8617, c_13129])).
% 12.75/4.87  tff(c_13175, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7944, c_13146])).
% 12.75/4.87  tff(c_8074, plain, (![A_458, B_459]: (r1_tarski(k1_tops_1(A_458, k2_pre_topc(A_458, B_459)), B_459) | ~v4_tops_1(B_459, A_458) | ~m1_subset_1(B_459, k1_zfmisc_1(u1_struct_0(A_458))) | ~l1_pre_topc(A_458))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.75/4.87  tff(c_14573, plain, (![A_614, B_615]: (k1_tops_1(A_614, k2_pre_topc(A_614, B_615))=B_615 | ~r1_tarski(B_615, k1_tops_1(A_614, k2_pre_topc(A_614, B_615))) | ~v4_tops_1(B_615, A_614) | ~m1_subset_1(B_615, k1_zfmisc_1(u1_struct_0(A_614))) | ~l1_pre_topc(A_614))), inference(resolution, [status(thm)], [c_8074, c_2])).
% 12.75/4.87  tff(c_14588, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_13175, c_14573])).
% 12.75/4.87  tff(c_14630, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_5725, c_14588])).
% 12.75/4.87  tff(c_8618, plain, (m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_8472])).
% 12.75/4.87  tff(c_22, plain, (![B_15, A_13]: (v6_tops_1(B_15, A_13) | k1_tops_1(A_13, k2_pre_topc(A_13, B_15))!=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.75/4.87  tff(c_8451, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8436, c_22])).
% 12.75/4.87  tff(c_8470, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8451])).
% 12.75/4.87  tff(c_9094, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8618, c_8470])).
% 12.75/4.87  tff(c_14655, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14630, c_9094])).
% 12.75/4.87  tff(c_14665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_14655])).
% 12.75/4.87  tff(c_14667, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 12.75/4.87  tff(c_56, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.87  tff(c_14668, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_14667, c_56])).
% 12.75/4.87  tff(c_14724, plain, (![A_627, B_628]: (r1_tarski(k1_tops_1(A_627, B_628), B_628) | ~m1_subset_1(B_628, k1_zfmisc_1(u1_struct_0(A_627))) | ~l1_pre_topc(A_627))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.75/4.87  tff(c_14729, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_14724])).
% 12.75/4.87  tff(c_14735, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14729])).
% 12.75/4.87  tff(c_14744, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_14735, c_2])).
% 12.75/4.87  tff(c_14766, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_14744])).
% 12.75/4.87  tff(c_14666, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 12.75/4.87  tff(c_16347, plain, (![B_699, A_700, C_701]: (r1_tarski(B_699, k1_tops_1(A_700, C_701)) | ~r1_tarski(B_699, C_701) | ~v3_pre_topc(B_699, A_700) | ~m1_subset_1(C_701, k1_zfmisc_1(u1_struct_0(A_700))) | ~m1_subset_1(B_699, k1_zfmisc_1(u1_struct_0(A_700))) | ~l1_pre_topc(A_700))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.75/4.87  tff(c_16358, plain, (![B_699]: (r1_tarski(B_699, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_699, '#skF_4') | ~v3_pre_topc(B_699, '#skF_2') | ~m1_subset_1(B_699, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_16347])).
% 12.75/4.87  tff(c_16485, plain, (![B_705]: (r1_tarski(B_705, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_705, '#skF_4') | ~v3_pre_topc(B_705, '#skF_2') | ~m1_subset_1(B_705, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16358])).
% 12.75/4.87  tff(c_16502, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_16485])).
% 12.75/4.87  tff(c_16511, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_6, c_16502])).
% 12.75/4.87  tff(c_16513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14766, c_16511])).
% 12.75/4.87  tff(c_16514, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_14744])).
% 12.75/4.87  tff(c_17295, plain, (![B_752, A_753]: (r1_tarski(B_752, k2_pre_topc(A_753, k1_tops_1(A_753, B_752))) | ~v4_tops_1(B_752, A_753) | ~m1_subset_1(B_752, k1_zfmisc_1(u1_struct_0(A_753))) | ~l1_pre_topc(A_753))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.75/4.87  tff(c_17337, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16514, c_17295])).
% 12.75/4.87  tff(c_17357, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_14668, c_17337])).
% 12.75/4.87  tff(c_16572, plain, (![A_709, B_710]: (m1_subset_1(k2_pre_topc(A_709, B_710), k1_zfmisc_1(u1_struct_0(A_709))) | ~m1_subset_1(B_710, k1_zfmisc_1(u1_struct_0(A_709))) | ~l1_pre_topc(A_709))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/4.87  tff(c_28, plain, (![A_18, B_20]: (r1_tarski(k1_tops_1(A_18, B_20), B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.75/4.87  tff(c_16578, plain, (![A_709, B_710]: (r1_tarski(k1_tops_1(A_709, k2_pre_topc(A_709, B_710)), k2_pre_topc(A_709, B_710)) | ~m1_subset_1(B_710, k1_zfmisc_1(u1_struct_0(A_709))) | ~l1_pre_topc(A_709))), inference(resolution, [status(thm)], [c_16572, c_28])).
% 12.75/4.87  tff(c_16685, plain, (![A_719, B_720]: (r1_tarski(k2_pre_topc(A_719, B_720), u1_struct_0(A_719)) | ~m1_subset_1(B_720, k1_zfmisc_1(u1_struct_0(A_719))) | ~l1_pre_topc(A_719))), inference(resolution, [status(thm)], [c_16572, c_10])).
% 12.75/4.87  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.75/4.87  tff(c_17250, plain, (![A_747, A_748, B_749]: (r1_tarski(A_747, u1_struct_0(A_748)) | ~r1_tarski(A_747, k2_pre_topc(A_748, B_749)) | ~m1_subset_1(B_749, k1_zfmisc_1(u1_struct_0(A_748))) | ~l1_pre_topc(A_748))), inference(resolution, [status(thm)], [c_16685, c_8])).
% 12.75/4.87  tff(c_17259, plain, (![A_709, B_710]: (r1_tarski(k1_tops_1(A_709, k2_pre_topc(A_709, B_710)), u1_struct_0(A_709)) | ~m1_subset_1(B_710, k1_zfmisc_1(u1_struct_0(A_709))) | ~l1_pre_topc(A_709))), inference(resolution, [status(thm)], [c_16578, c_17250])).
% 12.75/4.87  tff(c_17785, plain, (![A_769, B_770]: (k2_pre_topc(A_769, k1_tops_1(A_769, k2_pre_topc(A_769, B_770)))=k2_pre_topc(A_769, B_770) | ~v3_pre_topc(B_770, A_769) | ~m1_subset_1(B_770, k1_zfmisc_1(u1_struct_0(A_769))) | ~l1_pre_topc(A_769))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.75/4.87  tff(c_17792, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_17785])).
% 12.75/4.87  tff(c_17799, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14666, c_17792])).
% 12.75/4.87  tff(c_16579, plain, (![A_709, B_710]: (r1_tarski(k2_pre_topc(A_709, B_710), u1_struct_0(A_709)) | ~m1_subset_1(B_710, k1_zfmisc_1(u1_struct_0(A_709))) | ~l1_pre_topc(A_709))), inference(resolution, [status(thm)], [c_16572, c_10])).
% 12.75/4.87  tff(c_17834, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17799, c_16579])).
% 12.75/4.87  tff(c_17862, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_17834])).
% 12.75/4.87  tff(c_17869, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_17862])).
% 12.75/4.87  tff(c_17878, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_17869])).
% 12.75/4.87  tff(c_17881, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_17259, c_17878])).
% 12.75/4.87  tff(c_17894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_17881])).
% 12.75/4.87  tff(c_17895, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_17862])).
% 12.75/4.87  tff(c_18184, plain, (![B_777, A_778, C_779]: (r1_tarski(B_777, k1_tops_1(A_778, C_779)) | ~r1_tarski(B_777, C_779) | ~v3_pre_topc(B_777, A_778) | ~m1_subset_1(C_779, k1_zfmisc_1(u1_struct_0(A_778))) | ~m1_subset_1(B_777, k1_zfmisc_1(u1_struct_0(A_778))) | ~l1_pre_topc(A_778))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.75/4.87  tff(c_21214, plain, (![B_858, A_859, A_860]: (r1_tarski(B_858, k1_tops_1(A_859, A_860)) | ~r1_tarski(B_858, A_860) | ~v3_pre_topc(B_858, A_859) | ~m1_subset_1(B_858, k1_zfmisc_1(u1_struct_0(A_859))) | ~l1_pre_topc(A_859) | ~r1_tarski(A_860, u1_struct_0(A_859)))), inference(resolution, [status(thm)], [c_12, c_18184])).
% 12.75/4.87  tff(c_21225, plain, (![A_860]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', A_860)) | ~r1_tarski('#skF_4', A_860) | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_860, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_38, c_21214])).
% 12.75/4.87  tff(c_21242, plain, (![A_861]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', A_861)) | ~r1_tarski('#skF_4', A_861) | ~r1_tarski(A_861, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14666, c_21225])).
% 12.75/4.87  tff(c_21250, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_17895, c_21242])).
% 12.75/4.87  tff(c_21280, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_17357, c_21250])).
% 12.75/4.87  tff(c_21401, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(resolution, [status(thm)], [c_21280, c_2])).
% 12.75/4.87  tff(c_21964, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_21401])).
% 12.75/4.87  tff(c_21970, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_21964])).
% 12.75/4.87  tff(c_21979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_14668, c_21970])).
% 12.75/4.87  tff(c_21980, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_21401])).
% 12.75/4.87  tff(c_17896, plain, (m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_17862])).
% 12.75/4.87  tff(c_17828, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17799, c_22])).
% 12.75/4.87  tff(c_17859, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_17828])).
% 12.75/4.87  tff(c_18069, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17896, c_17859])).
% 12.75/4.87  tff(c_22020, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21980, c_18069])).
% 12.75/4.87  tff(c_22029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_22020])).
% 12.75/4.87  tff(c_22031, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 12.75/4.87  tff(c_48, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.75/4.87  tff(c_22064, plain, (~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22031, c_48])).
% 12.75/4.87  tff(c_22065, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_22064])).
% 12.75/4.87  tff(c_22030, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 12.75/4.87  tff(c_22710, plain, (![A_921, B_922]: (k1_tops_1(A_921, k2_pre_topc(A_921, B_922))=B_922 | ~v6_tops_1(B_922, A_921) | ~m1_subset_1(B_922, k1_zfmisc_1(u1_struct_0(A_921))) | ~l1_pre_topc(A_921))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.75/4.87  tff(c_22719, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_22710])).
% 12.75/4.87  tff(c_22727, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22030, c_22719])).
% 12.75/4.87  tff(c_22243, plain, (![A_893, B_894]: (m1_subset_1(k2_pre_topc(A_893, B_894), k1_zfmisc_1(u1_struct_0(A_893))) | ~m1_subset_1(B_894, k1_zfmisc_1(u1_struct_0(A_893))) | ~l1_pre_topc(A_893))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/4.87  tff(c_22250, plain, (![A_893, B_894]: (r1_tarski(k2_pre_topc(A_893, B_894), u1_struct_0(A_893)) | ~m1_subset_1(B_894, k1_zfmisc_1(u1_struct_0(A_893))) | ~l1_pre_topc(A_893))), inference(resolution, [status(thm)], [c_22243, c_10])).
% 12.75/4.87  tff(c_22158, plain, (![A_889, B_890]: (r1_tarski(k1_tops_1(A_889, B_890), B_890) | ~m1_subset_1(B_890, k1_zfmisc_1(u1_struct_0(A_889))) | ~l1_pre_topc(A_889))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.75/4.87  tff(c_22166, plain, (![A_889, A_6]: (r1_tarski(k1_tops_1(A_889, A_6), A_6) | ~l1_pre_topc(A_889) | ~r1_tarski(A_6, u1_struct_0(A_889)))), inference(resolution, [status(thm)], [c_12, c_22158])).
% 12.75/4.87  tff(c_22784, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22727, c_22166])).
% 12.75/4.87  tff(c_22800, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22784])).
% 12.75/4.87  tff(c_22804, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_22800])).
% 12.75/4.87  tff(c_22807, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22250, c_22804])).
% 12.75/4.87  tff(c_22814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_22807])).
% 12.75/4.87  tff(c_22816, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_22800])).
% 12.75/4.87  tff(c_22300, plain, (![A_899, B_900]: (k1_tops_1(A_899, k1_tops_1(A_899, B_900))=k1_tops_1(A_899, B_900) | ~m1_subset_1(B_900, k1_zfmisc_1(u1_struct_0(A_899))) | ~l1_pre_topc(A_899))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.75/4.87  tff(c_22311, plain, (![A_899, A_6]: (k1_tops_1(A_899, k1_tops_1(A_899, A_6))=k1_tops_1(A_899, A_6) | ~l1_pre_topc(A_899) | ~r1_tarski(A_6, u1_struct_0(A_899)))), inference(resolution, [status(thm)], [c_12, c_22300])).
% 12.75/4.87  tff(c_22882, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22816, c_22311])).
% 12.75/4.87  tff(c_22893, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22727, c_22727, c_22882])).
% 12.75/4.87  tff(c_22165, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_22158])).
% 12.75/4.87  tff(c_22172, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22165])).
% 12.75/4.87  tff(c_22200, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_22172, c_2])).
% 12.75/4.87  tff(c_22241, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_22200])).
% 12.75/4.87  tff(c_22903, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22893, c_22241])).
% 12.75/4.87  tff(c_22909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_22903])).
% 12.75/4.87  tff(c_22910, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_22200])).
% 12.75/4.87  tff(c_24659, plain, (![D_1000, B_1001]: (~m1_subset_1(D_1000, k1_zfmisc_1(u1_struct_0(B_1001))) | ~l1_pre_topc(B_1001))), inference(splitLeft, [status(thm)], [c_30])).
% 12.75/4.87  tff(c_24666, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_24659])).
% 12.75/4.87  tff(c_24674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_24666])).
% 12.75/4.87  tff(c_24755, plain, (![C_1004, A_1005]: (v3_pre_topc(C_1004, A_1005) | k1_tops_1(A_1005, C_1004)!=C_1004 | ~m1_subset_1(C_1004, k1_zfmisc_1(u1_struct_0(A_1005))) | ~l1_pre_topc(A_1005) | ~v2_pre_topc(A_1005))), inference(splitRight, [status(thm)], [c_30])).
% 12.75/4.87  tff(c_24768, plain, (v3_pre_topc('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_24755])).
% 12.75/4.87  tff(c_24776, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_22910, c_24768])).
% 12.75/4.87  tff(c_24778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22065, c_24776])).
% 12.75/4.87  tff(c_24779, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_22064])).
% 12.75/4.87  tff(c_26084, plain, (![A_1078, B_1079]: (m1_subset_1(k2_pre_topc(A_1078, B_1079), k1_zfmisc_1(u1_struct_0(A_1078))) | ~m1_subset_1(B_1079, k1_zfmisc_1(u1_struct_0(A_1078))) | ~l1_pre_topc(A_1078))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/4.87  tff(c_26091, plain, (![A_1078, B_1079]: (r1_tarski(k2_pre_topc(A_1078, B_1079), u1_struct_0(A_1078)) | ~m1_subset_1(B_1079, k1_zfmisc_1(u1_struct_0(A_1078))) | ~l1_pre_topc(A_1078))), inference(resolution, [status(thm)], [c_26084, c_10])).
% 12.75/4.87  tff(c_26999, plain, (![A_1132, B_1133]: (k1_tops_1(A_1132, k2_pre_topc(A_1132, B_1133))=B_1133 | ~v6_tops_1(B_1133, A_1132) | ~m1_subset_1(B_1133, k1_zfmisc_1(u1_struct_0(A_1132))) | ~l1_pre_topc(A_1132))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.75/4.87  tff(c_27008, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_26999])).
% 12.75/4.87  tff(c_27016, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22030, c_27008])).
% 12.75/4.87  tff(c_24827, plain, (![A_1013, B_1014]: (r1_tarski(k1_tops_1(A_1013, B_1014), B_1014) | ~m1_subset_1(B_1014, k1_zfmisc_1(u1_struct_0(A_1013))) | ~l1_pre_topc(A_1013))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.75/4.87  tff(c_24835, plain, (![A_1013, A_6]: (r1_tarski(k1_tops_1(A_1013, A_6), A_6) | ~l1_pre_topc(A_1013) | ~r1_tarski(A_6, u1_struct_0(A_1013)))), inference(resolution, [status(thm)], [c_12, c_24827])).
% 12.75/4.87  tff(c_27073, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_27016, c_24835])).
% 12.75/4.87  tff(c_27089, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_27073])).
% 12.75/4.87  tff(c_27273, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_27089])).
% 12.75/4.87  tff(c_27276, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26091, c_27273])).
% 12.75/4.87  tff(c_27283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_27276])).
% 12.75/4.87  tff(c_27284, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_27089])).
% 12.75/4.87  tff(c_25861, plain, (![A_1074, B_1075]: (k1_tops_1(A_1074, k2_pre_topc(A_1074, B_1075))=B_1075 | ~v6_tops_1(B_1075, A_1074) | ~m1_subset_1(B_1075, k1_zfmisc_1(u1_struct_0(A_1074))) | ~l1_pre_topc(A_1074))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.75/4.87  tff(c_25870, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_25861])).
% 12.75/4.87  tff(c_25878, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22030, c_25870])).
% 12.75/4.87  tff(c_25433, plain, (![A_1046, B_1047]: (m1_subset_1(k2_pre_topc(A_1046, B_1047), k1_zfmisc_1(u1_struct_0(A_1046))) | ~m1_subset_1(B_1047, k1_zfmisc_1(u1_struct_0(A_1046))) | ~l1_pre_topc(A_1046))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/4.87  tff(c_25440, plain, (![A_1046, B_1047]: (r1_tarski(k2_pre_topc(A_1046, B_1047), u1_struct_0(A_1046)) | ~m1_subset_1(B_1047, k1_zfmisc_1(u1_struct_0(A_1046))) | ~l1_pre_topc(A_1046))), inference(resolution, [status(thm)], [c_25433, c_10])).
% 12.75/4.87  tff(c_25935, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_25878, c_24835])).
% 12.75/4.87  tff(c_25951, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_25935])).
% 12.75/4.87  tff(c_26011, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_25951])).
% 12.75/4.87  tff(c_26018, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_25440, c_26011])).
% 12.75/4.87  tff(c_26028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_26018])).
% 12.75/4.87  tff(c_26030, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_25951])).
% 12.75/4.87  tff(c_25487, plain, (![A_1051, B_1052]: (k1_tops_1(A_1051, k1_tops_1(A_1051, B_1052))=k1_tops_1(A_1051, B_1052) | ~m1_subset_1(B_1052, k1_zfmisc_1(u1_struct_0(A_1051))) | ~l1_pre_topc(A_1051))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.75/4.87  tff(c_25498, plain, (![A_1051, A_6]: (k1_tops_1(A_1051, k1_tops_1(A_1051, A_6))=k1_tops_1(A_1051, A_6) | ~l1_pre_topc(A_1051) | ~r1_tarski(A_6, u1_struct_0(A_1051)))), inference(resolution, [status(thm)], [c_12, c_25487])).
% 12.75/4.87  tff(c_26045, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26030, c_25498])).
% 12.75/4.87  tff(c_26056, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_25878, c_25878, c_26045])).
% 12.75/4.87  tff(c_24834, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_24827])).
% 12.75/4.87  tff(c_24841, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_24834])).
% 12.75/4.87  tff(c_24861, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24841, c_2])).
% 12.75/4.87  tff(c_24886, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_24861])).
% 12.75/4.87  tff(c_26066, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26056, c_24886])).
% 12.75/4.87  tff(c_26072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_26066])).
% 12.75/4.87  tff(c_26073, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_24861])).
% 12.75/4.87  tff(c_28354, plain, (![B_1184, A_1185]: (v4_tops_1(B_1184, A_1185) | ~r1_tarski(B_1184, k2_pre_topc(A_1185, k1_tops_1(A_1185, B_1184))) | ~r1_tarski(k1_tops_1(A_1185, k2_pre_topc(A_1185, B_1184)), B_1184) | ~m1_subset_1(B_1184, k1_zfmisc_1(u1_struct_0(A_1185))) | ~l1_pre_topc(A_1185))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.75/4.87  tff(c_28381, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_27016, c_28354])).
% 12.75/4.87  tff(c_28412, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_6, c_27284, c_26073, c_28381])).
% 12.75/4.87  tff(c_28414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24779, c_28412])).
% 12.75/4.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.75/4.87  
% 12.75/4.87  Inference rules
% 12.75/4.87  ----------------------
% 12.75/4.87  #Ref     : 0
% 12.75/4.87  #Sup     : 6353
% 12.75/4.87  #Fact    : 0
% 12.75/4.87  #Define  : 0
% 12.75/4.87  #Split   : 227
% 12.75/4.87  #Chain   : 0
% 12.75/4.87  #Close   : 0
% 12.75/4.87  
% 12.75/4.87  Ordering : KBO
% 12.75/4.87  
% 12.75/4.87  Simplification rules
% 12.75/4.87  ----------------------
% 12.75/4.87  #Subsume      : 2208
% 12.75/4.87  #Demod        : 4894
% 12.75/4.87  #Tautology    : 1459
% 12.75/4.87  #SimpNegUnit  : 40
% 12.75/4.87  #BackRed      : 98
% 12.75/4.87  
% 12.75/4.87  #Partial instantiations: 0
% 12.75/4.87  #Strategies tried      : 1
% 12.75/4.87  
% 12.75/4.87  Timing (in seconds)
% 12.75/4.87  ----------------------
% 12.75/4.87  Preprocessing        : 0.34
% 12.75/4.87  Parsing              : 0.19
% 12.75/4.87  CNF conversion       : 0.03
% 12.75/4.87  Main loop            : 3.70
% 12.75/4.87  Inferencing          : 0.96
% 12.75/4.87  Reduction            : 1.26
% 12.75/4.87  Demodulation         : 0.87
% 12.75/4.87  BG Simplification    : 0.11
% 12.75/4.87  Subsumption          : 1.14
% 12.75/4.87  Abstraction          : 0.16
% 12.75/4.87  MUC search           : 0.00
% 12.75/4.87  Cooper               : 0.00
% 12.75/4.87  Total                : 4.14
% 12.75/4.87  Index Insertion      : 0.00
% 12.75/4.87  Index Deletion       : 0.00
% 12.75/4.87  Index Matching       : 0.00
% 12.75/4.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
