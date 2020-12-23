%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:24 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 819 expanded)
%              Number of leaves         :   28 ( 290 expanded)
%              Depth                    :   14
%              Number of atoms          :  541 (3372 expanded)
%              Number of equality atoms :   62 ( 186 expanded)
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

tff(f_137,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_111,axiom,(
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

tff(c_46,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3989,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_55,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_66,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_127,plain,(
    ! [A_62,B_63] :
      ( k1_tops_1(A_62,k2_pre_topc(A_62,B_63)) = B_63
      | ~ v6_tops_1(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_133,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_127])).

tff(c_140,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_133])).

tff(c_97,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k2_pre_topc(A_58,B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v3_pre_topc(k1_tops_1(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_184,plain,(
    ! [A_70,B_71] :
      ( v3_pre_topc(k1_tops_1(A_70,k2_pre_topc(A_70,B_71)),A_70)
      | ~ v2_pre_topc(A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_97,c_20])).

tff(c_187,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_184])).

tff(c_189,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_40,c_187])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_189])).

tff(c_193,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_192,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_194,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_400,plain,(
    ! [A_102,B_103] :
      ( k1_tops_1(A_102,k2_pre_topc(A_102,B_103)) = B_103
      | ~ v6_tops_1(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_406,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_400])).

tff(c_413,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_406])).

tff(c_374,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k2_pre_topc(A_96,B_97),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k1_tops_1(A_15,B_17),B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_429,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_tops_1(A_106,k2_pre_topc(A_106,B_107)),k2_pre_topc(A_106,B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_374,c_24])).

tff(c_434,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_429])).

tff(c_437,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_434])).

tff(c_259,plain,(
    ! [A_80,B_81] :
      ( k1_tops_1(A_80,k2_pre_topc(A_80,B_81)) = B_81
      | ~ v6_tops_1(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_265,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_259])).

tff(c_272,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_265])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_237,plain,(
    ! [A_78,B_79] :
      ( k1_tops_1(A_78,k1_tops_1(A_78,B_79)) = k1_tops_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_330,plain,(
    ! [A_92,B_93] :
      ( k1_tops_1(A_92,k1_tops_1(A_92,k2_pre_topc(A_92,B_93))) = k1_tops_1(A_92,k2_pre_topc(A_92,B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_237])).

tff(c_336,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_330])).

tff(c_343,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_272,c_272,c_336])).

tff(c_199,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k1_tops_1(A_72,B_73),B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_203,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_199])).

tff(c_209,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_203])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_217,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_346,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_217])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_346])).

tff(c_352,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_753,plain,(
    ! [B_135,A_136] :
      ( v4_tops_1(B_135,A_136)
      | ~ r1_tarski(B_135,k2_pre_topc(A_136,k1_tops_1(A_136,B_135)))
      | ~ r1_tarski(k1_tops_1(A_136,k2_pre_topc(A_136,B_135)),B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_767,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_753])).

tff(c_775,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_6,c_437,c_352,c_767])).

tff(c_777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_775])).

tff(c_779,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_44,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_783,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_779,c_44])).

tff(c_778,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_1007,plain,(
    ! [A_168,B_169] :
      ( k1_tops_1(A_168,k2_pre_topc(A_168,B_169)) = B_169
      | ~ v6_tops_1(B_169,A_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1013,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1007])).

tff(c_1020,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_1013])).

tff(c_1100,plain,(
    ! [A_180,B_181,C_182] :
      ( r1_tarski(k1_tops_1(A_180,B_181),k1_tops_1(A_180,C_182))
      | ~ r1_tarski(B_181,C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1111,plain,(
    ! [C_182] :
      ( r1_tarski('#skF_3',k1_tops_1('#skF_1',C_182))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_1100])).

tff(c_1133,plain,(
    ! [C_182] :
      ( r1_tarski('#skF_3',k1_tops_1('#skF_1',C_182))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1111])).

tff(c_1252,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1133])).

tff(c_1280,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1252])).

tff(c_1284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_1280])).

tff(c_1286,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1133])).

tff(c_30,plain,(
    ! [B_33,D_39,C_37,A_25] :
      ( k1_tops_1(B_33,D_39) = D_39
      | ~ v3_pre_topc(D_39,B_33)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(u1_struct_0(B_33)))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(B_33)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1668,plain,(
    ! [C_211,A_212] :
      ( ~ m1_subset_1(C_211,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212)
      | ~ v2_pre_topc(A_212) ) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_1674,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1286,c_1668])).

tff(c_1690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1674])).

tff(c_1692,plain,(
    ! [B_213,D_214] :
      ( k1_tops_1(B_213,D_214) = D_214
      | ~ v3_pre_topc(D_214,B_213)
      | ~ m1_subset_1(D_214,k1_zfmisc_1(u1_struct_0(B_213)))
      | ~ l1_pre_topc(B_213) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1704,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1692])).

tff(c_1717,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_778,c_1704])).

tff(c_784,plain,(
    ! [A_137,B_138] :
      ( r1_tarski(k1_tops_1(A_137,B_138),B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_786,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_784])).

tff(c_791,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_786])).

tff(c_797,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_791,c_2])).

tff(c_801,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_1725,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1717,c_801])).

tff(c_1731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1725])).

tff(c_1732,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_2073,plain,(
    ! [B_254,A_255] :
      ( r1_tarski(B_254,k2_pre_topc(A_255,k1_tops_1(A_255,B_254)))
      | ~ v4_tops_1(B_254,A_255)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2084,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_2073])).

tff(c_2091,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_783,c_2084])).

tff(c_2119,plain,(
    ! [A_258,B_259,C_260] :
      ( r1_tarski(k1_tops_1(A_258,B_259),k1_tops_1(A_258,C_260))
      | ~ r1_tarski(B_259,C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2142,plain,(
    ! [C_260] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_260))
      | ~ r1_tarski('#skF_4',C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_2119])).

tff(c_2191,plain,(
    ! [C_263] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_263))
      | ~ r1_tarski('#skF_4',C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_2142])).

tff(c_2195,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_2191])).

tff(c_2201,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2195])).

tff(c_2060,plain,(
    ! [A_252,B_253] :
      ( r1_tarski(k1_tops_1(A_252,k2_pre_topc(A_252,B_253)),B_253)
      | ~ v4_tops_1(B_253,A_252)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3088,plain,(
    ! [A_320,B_321] :
      ( k1_tops_1(A_320,k2_pre_topc(A_320,B_321)) = B_321
      | ~ r1_tarski(B_321,k1_tops_1(A_320,k2_pre_topc(A_320,B_321)))
      | ~ v4_tops_1(B_321,A_320)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_pre_topc(A_320) ) ),
    inference(resolution,[status(thm)],[c_2060,c_2])).

tff(c_3096,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2201,c_3088])).

tff(c_3113,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2091,c_36,c_783,c_3096])).

tff(c_16,plain,(
    ! [B_10,A_8] :
      ( v6_tops_1(B_10,A_8)
      | k1_tops_1(A_8,k2_pre_topc(A_8,B_10)) != B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3168,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3113,c_16])).

tff(c_3195,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_3168])).

tff(c_3197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_3195])).

tff(c_3199,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3200,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_3201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3199,c_3200])).

tff(c_3202,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3198,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3544,plain,(
    ! [C_359,A_360] :
      ( ~ m1_subset_1(C_359,k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360) ) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_3556,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_3544])).

tff(c_3567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3556])).

tff(c_3569,plain,(
    ! [B_361,D_362] :
      ( k1_tops_1(B_361,D_362) = D_362
      | ~ v3_pre_topc(D_362,B_361)
      | ~ m1_subset_1(D_362,k1_zfmisc_1(u1_struct_0(B_361)))
      | ~ l1_pre_topc(B_361) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_3578,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_3569])).

tff(c_3588,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3198,c_3578])).

tff(c_3213,plain,(
    ! [A_324,B_325] :
      ( r1_tarski(k1_tops_1(A_324,B_325),B_325)
      | ~ m1_subset_1(B_325,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3215,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_3213])).

tff(c_3220,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3215])).

tff(c_3226,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_3220,c_2])).

tff(c_3230,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3226])).

tff(c_3597,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3588,c_3230])).

tff(c_3603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3597])).

tff(c_3604,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3226])).

tff(c_3674,plain,(
    ! [B_379,A_380] :
      ( r1_tarski(B_379,k2_pre_topc(A_380,k1_tops_1(A_380,B_379)))
      | ~ v4_tops_1(B_379,A_380)
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ l1_pre_topc(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3682,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3604,c_3674])).

tff(c_3687,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_3202,c_3682])).

tff(c_3725,plain,(
    ! [A_383,B_384,C_385] :
      ( r1_tarski(k1_tops_1(A_383,B_384),k1_tops_1(A_383,C_385))
      | ~ r1_tarski(B_384,C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(u1_struct_0(A_383)))
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0(A_383)))
      | ~ l1_pre_topc(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3748,plain,(
    ! [C_385] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_385))
      | ~ r1_tarski('#skF_4',C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3604,c_3725])).

tff(c_3769,plain,(
    ! [C_386] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_386))
      | ~ r1_tarski('#skF_4',C_386)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_3748])).

tff(c_3773,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_3769])).

tff(c_3779,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3773])).

tff(c_3670,plain,(
    ! [A_377,B_378] :
      ( r1_tarski(k1_tops_1(A_377,k2_pre_topc(A_377,B_378)),B_378)
      | ~ v4_tops_1(B_378,A_377)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3908,plain,(
    ! [A_404,B_405] :
      ( k1_tops_1(A_404,k2_pre_topc(A_404,B_405)) = B_405
      | ~ r1_tarski(B_405,k1_tops_1(A_404,k2_pre_topc(A_404,B_405)))
      | ~ v4_tops_1(B_405,A_404)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_3670,c_2])).

tff(c_3912,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_3779,c_3908])).

tff(c_3919,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3687,c_36,c_3202,c_3912])).

tff(c_3952,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3919,c_16])).

tff(c_3975,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_3952])).

tff(c_3977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_3975])).

tff(c_3978,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4052,plain,(
    ! [A_416,B_417] :
      ( k1_tops_1(A_416,k2_pre_topc(A_416,B_417)) = B_417
      | ~ v6_tops_1(B_417,A_416)
      | ~ m1_subset_1(B_417,k1_zfmisc_1(u1_struct_0(A_416)))
      | ~ l1_pre_topc(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4058,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4052])).

tff(c_4065,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3978,c_4058])).

tff(c_4023,plain,(
    ! [A_412,B_413] :
      ( m1_subset_1(k2_pre_topc(A_412,B_413),k1_zfmisc_1(u1_struct_0(A_412)))
      | ~ m1_subset_1(B_413,k1_zfmisc_1(u1_struct_0(A_412)))
      | ~ l1_pre_topc(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4121,plain,(
    ! [A_424,B_425] :
      ( v3_pre_topc(k1_tops_1(A_424,k2_pre_topc(A_424,B_425)),A_424)
      | ~ v2_pre_topc(A_424)
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_424)))
      | ~ l1_pre_topc(A_424) ) ),
    inference(resolution,[status(thm)],[c_4023,c_20])).

tff(c_4124,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4065,c_4121])).

tff(c_4129,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_40,c_4124])).

tff(c_4131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3989,c_4129])).

tff(c_4133,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4132,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4134,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4132])).

tff(c_4857,plain,(
    ! [A_490,B_491] :
      ( k1_tops_1(A_490,k2_pre_topc(A_490,B_491)) = B_491
      | ~ v6_tops_1(B_491,A_490)
      | ~ m1_subset_1(B_491,k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ l1_pre_topc(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4863,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4857])).

tff(c_4870,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3978,c_4863])).

tff(c_4821,plain,(
    ! [A_482,B_483] :
      ( m1_subset_1(k2_pre_topc(A_482,B_483),k1_zfmisc_1(u1_struct_0(A_482)))
      | ~ m1_subset_1(B_483,k1_zfmisc_1(u1_struct_0(A_482)))
      | ~ l1_pre_topc(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4903,plain,(
    ! [A_494,B_495] :
      ( r1_tarski(k1_tops_1(A_494,k2_pre_topc(A_494,B_495)),k2_pre_topc(A_494,B_495))
      | ~ m1_subset_1(B_495,k1_zfmisc_1(u1_struct_0(A_494)))
      | ~ l1_pre_topc(A_494) ) ),
    inference(resolution,[status(thm)],[c_4821,c_24])).

tff(c_4908,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4870,c_4903])).

tff(c_4914,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_4908])).

tff(c_4415,plain,(
    ! [A_459,B_460] :
      ( k1_tops_1(A_459,k2_pre_topc(A_459,B_460)) = B_460
      | ~ v6_tops_1(B_460,A_459)
      | ~ m1_subset_1(B_460,k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ l1_pre_topc(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4421,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4415])).

tff(c_4428,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3978,c_4421])).

tff(c_4139,plain,(
    ! [A_426,B_427] :
      ( r1_tarski(k1_tops_1(A_426,B_427),B_427)
      | ~ m1_subset_1(B_427,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_pre_topc(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4143,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4139])).

tff(c_4149,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4143])).

tff(c_4155,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4149,c_2])).

tff(c_4375,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4155])).

tff(c_4395,plain,(
    ! [A_455,B_456] :
      ( k1_tops_1(A_455,k1_tops_1(A_455,B_456)) = k1_tops_1(A_455,B_456)
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0(A_455)))
      | ~ l1_pre_topc(A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4520,plain,(
    ! [A_469,B_470] :
      ( k1_tops_1(A_469,k1_tops_1(A_469,k2_pre_topc(A_469,B_470))) = k1_tops_1(A_469,k2_pre_topc(A_469,B_470))
      | ~ m1_subset_1(B_470,k1_zfmisc_1(u1_struct_0(A_469)))
      | ~ l1_pre_topc(A_469) ) ),
    inference(resolution,[status(thm)],[c_8,c_4395])).

tff(c_4526,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4520])).

tff(c_4533,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4428,c_4428,c_4526])).

tff(c_4401,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4395])).

tff(c_4408,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4401])).

tff(c_4472,plain,(
    ! [B_465,A_466] :
      ( r1_tarski(B_465,k2_pre_topc(A_466,k1_tops_1(A_466,B_465)))
      | ~ v4_tops_1(B_465,A_466)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_466)))
      | ~ l1_pre_topc(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4483,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4408,c_4472])).

tff(c_4493,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4483])).

tff(c_4503,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4493])).

tff(c_4534,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_4503])).

tff(c_4541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4534])).

tff(c_4543,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4493])).

tff(c_4646,plain,(
    ! [A_475,B_476,C_477] :
      ( r1_tarski(k1_tops_1(A_475,B_476),k1_tops_1(A_475,C_477))
      | ~ r1_tarski(B_476,C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ m1_subset_1(B_476,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ l1_pre_topc(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4672,plain,(
    ! [B_476] :
      ( r1_tarski(k1_tops_1('#skF_1',B_476),k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_476,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_476,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4408,c_4646])).

tff(c_4746,plain,(
    ! [B_481] :
      ( r1_tarski(k1_tops_1('#skF_1',B_481),k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_481,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_481,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4543,c_4672])).

tff(c_4754,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4428,c_4746])).

tff(c_4760,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4375,c_4754])).

tff(c_4763,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4760])).

tff(c_4766,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_4763])).

tff(c_4770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_4766])).

tff(c_4772,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4760])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( k1_tops_1(A_13,k1_tops_1(A_13,B_14)) = k1_tops_1(A_13,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4776,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4772,c_22])).

tff(c_4786,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4428,c_4428,c_4776])).

tff(c_4803,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4786,c_4375])).

tff(c_4812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4803])).

tff(c_4813,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4155])).

tff(c_4974,plain,(
    ! [A_502,B_503,C_504] :
      ( r1_tarski(k1_tops_1(A_502,B_503),k1_tops_1(A_502,C_504))
      | ~ r1_tarski(B_503,C_504)
      | ~ m1_subset_1(C_504,k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ m1_subset_1(B_503,k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ l1_pre_topc(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4979,plain,(
    ! [C_504] :
      ( r1_tarski('#skF_3',k1_tops_1('#skF_1',C_504))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),C_504)
      | ~ m1_subset_1(C_504,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4870,c_4974])).

tff(c_5003,plain,(
    ! [C_504] :
      ( r1_tarski('#skF_3',k1_tops_1('#skF_1',C_504))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),C_504)
      | ~ m1_subset_1(C_504,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4979])).

tff(c_5032,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5003])).

tff(c_5035,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_5032])).

tff(c_5039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_5035])).

tff(c_5041,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_5003])).

tff(c_4982,plain,(
    ! [B_503] :
      ( r1_tarski(k1_tops_1('#skF_1',B_503),'#skF_3')
      | ~ r1_tarski(B_503,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_503,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4870,c_4974])).

tff(c_5005,plain,(
    ! [B_503] :
      ( r1_tarski(k1_tops_1('#skF_1',B_503),'#skF_3')
      | ~ r1_tarski(B_503,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_503,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4982])).

tff(c_5255,plain,(
    ! [B_515] :
      ( r1_tarski(k1_tops_1('#skF_1',B_515),'#skF_3')
      | ~ r1_tarski(B_515,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_515,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5041,c_5005])).

tff(c_5262,plain,(
    ! [B_4] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',B_4)),'#skF_3')
      | ~ r1_tarski(k2_pre_topc('#skF_1',B_4),k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_5255])).

tff(c_5271,plain,(
    ! [B_4] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',B_4)),'#skF_3')
      | ~ r1_tarski(k2_pre_topc('#skF_1',B_4),k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5262])).

tff(c_5435,plain,(
    ! [B_526,A_527] :
      ( v4_tops_1(B_526,A_527)
      | ~ r1_tarski(B_526,k2_pre_topc(A_527,k1_tops_1(A_527,B_526)))
      | ~ r1_tarski(k1_tops_1(A_527,k2_pre_topc(A_527,B_526)),B_526)
      | ~ m1_subset_1(B_526,k1_zfmisc_1(u1_struct_0(A_527)))
      | ~ l1_pre_topc(A_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5439,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_5271,c_5435])).

tff(c_5463,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6,c_38,c_4914,c_4813,c_5439])).

tff(c_5465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4134,c_5463])).

tff(c_5467,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4132])).

tff(c_3979,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4133,c_5467,c_3979,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.36  
% 6.21/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.36  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.21/2.36  
% 6.21/2.36  %Foreground sorts:
% 6.21/2.36  
% 6.21/2.36  
% 6.21/2.36  %Background operators:
% 6.21/2.36  
% 6.21/2.36  
% 6.21/2.36  %Foreground operators:
% 6.21/2.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.21/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.36  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 6.21/2.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.21/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.36  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 6.21/2.36  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.21/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.21/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.21/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.21/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.21/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.21/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.21/2.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.21/2.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.21/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.21/2.36  
% 6.64/2.40  tff(f_137, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 6.64/2.40  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 6.64/2.40  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.64/2.40  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.64/2.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.64/2.40  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.64/2.40  tff(f_71, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 6.64/2.40  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 6.64/2.40  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 6.64/2.40  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 6.64/2.40  tff(c_46, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_3989, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 6.64/2.40  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_48, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_55, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 6.64/2.40  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_66, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 6.64/2.40  tff(c_52, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_56, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 6.64/2.40  tff(c_127, plain, (![A_62, B_63]: (k1_tops_1(A_62, k2_pre_topc(A_62, B_63))=B_63 | ~v6_tops_1(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.40  tff(c_133, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_127])).
% 6.64/2.40  tff(c_140, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_133])).
% 6.64/2.40  tff(c_97, plain, (![A_58, B_59]: (m1_subset_1(k2_pre_topc(A_58, B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.64/2.40  tff(c_20, plain, (![A_11, B_12]: (v3_pre_topc(k1_tops_1(A_11, B_12), A_11) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.64/2.40  tff(c_184, plain, (![A_70, B_71]: (v3_pre_topc(k1_tops_1(A_70, k2_pre_topc(A_70, B_71)), A_70) | ~v2_pre_topc(A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_97, c_20])).
% 6.64/2.40  tff(c_187, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_140, c_184])).
% 6.64/2.40  tff(c_189, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_40, c_187])).
% 6.64/2.40  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_189])).
% 6.64/2.40  tff(c_193, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 6.64/2.40  tff(c_192, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 6.64/2.40  tff(c_194, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_192])).
% 6.64/2.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.64/2.40  tff(c_400, plain, (![A_102, B_103]: (k1_tops_1(A_102, k2_pre_topc(A_102, B_103))=B_103 | ~v6_tops_1(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.40  tff(c_406, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_400])).
% 6.64/2.40  tff(c_413, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_406])).
% 6.64/2.40  tff(c_374, plain, (![A_96, B_97]: (m1_subset_1(k2_pre_topc(A_96, B_97), k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.64/2.40  tff(c_24, plain, (![A_15, B_17]: (r1_tarski(k1_tops_1(A_15, B_17), B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.64/2.40  tff(c_429, plain, (![A_106, B_107]: (r1_tarski(k1_tops_1(A_106, k2_pre_topc(A_106, B_107)), k2_pre_topc(A_106, B_107)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_374, c_24])).
% 6.64/2.40  tff(c_434, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_413, c_429])).
% 6.64/2.40  tff(c_437, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_434])).
% 6.64/2.40  tff(c_259, plain, (![A_80, B_81]: (k1_tops_1(A_80, k2_pre_topc(A_80, B_81))=B_81 | ~v6_tops_1(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.40  tff(c_265, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_259])).
% 6.64/2.40  tff(c_272, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_265])).
% 6.64/2.40  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.64/2.40  tff(c_237, plain, (![A_78, B_79]: (k1_tops_1(A_78, k1_tops_1(A_78, B_79))=k1_tops_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.64/2.40  tff(c_330, plain, (![A_92, B_93]: (k1_tops_1(A_92, k1_tops_1(A_92, k2_pre_topc(A_92, B_93)))=k1_tops_1(A_92, k2_pre_topc(A_92, B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_8, c_237])).
% 6.64/2.40  tff(c_336, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_330])).
% 6.64/2.40  tff(c_343, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_272, c_272, c_336])).
% 6.64/2.40  tff(c_199, plain, (![A_72, B_73]: (r1_tarski(k1_tops_1(A_72, B_73), B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.64/2.40  tff(c_203, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_199])).
% 6.64/2.40  tff(c_209, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_203])).
% 6.64/2.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.64/2.40  tff(c_215, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_209, c_2])).
% 6.64/2.40  tff(c_217, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_215])).
% 6.64/2.40  tff(c_346, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_217])).
% 6.64/2.40  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_346])).
% 6.64/2.40  tff(c_352, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_215])).
% 6.64/2.40  tff(c_753, plain, (![B_135, A_136]: (v4_tops_1(B_135, A_136) | ~r1_tarski(B_135, k2_pre_topc(A_136, k1_tops_1(A_136, B_135))) | ~r1_tarski(k1_tops_1(A_136, k2_pre_topc(A_136, B_135)), B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.64/2.40  tff(c_767, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_413, c_753])).
% 6.64/2.40  tff(c_775, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_6, c_437, c_352, c_767])).
% 6.64/2.40  tff(c_777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_775])).
% 6.64/2.40  tff(c_779, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_192])).
% 6.64/2.40  tff(c_44, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_783, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_779, c_44])).
% 6.64/2.40  tff(c_778, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_192])).
% 6.64/2.40  tff(c_1007, plain, (![A_168, B_169]: (k1_tops_1(A_168, k2_pre_topc(A_168, B_169))=B_169 | ~v6_tops_1(B_169, A_168) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.40  tff(c_1013, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1007])).
% 6.64/2.40  tff(c_1020, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_1013])).
% 6.64/2.40  tff(c_1100, plain, (![A_180, B_181, C_182]: (r1_tarski(k1_tops_1(A_180, B_181), k1_tops_1(A_180, C_182)) | ~r1_tarski(B_181, C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.64/2.40  tff(c_1111, plain, (![C_182]: (r1_tarski('#skF_3', k1_tops_1('#skF_1', C_182)) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1020, c_1100])).
% 6.64/2.40  tff(c_1133, plain, (![C_182]: (r1_tarski('#skF_3', k1_tops_1('#skF_1', C_182)) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1111])).
% 6.64/2.40  tff(c_1252, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1133])).
% 6.64/2.40  tff(c_1280, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_1252])).
% 6.64/2.40  tff(c_1284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_1280])).
% 6.64/2.40  tff(c_1286, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1133])).
% 6.64/2.40  tff(c_30, plain, (![B_33, D_39, C_37, A_25]: (k1_tops_1(B_33, D_39)=D_39 | ~v3_pre_topc(D_39, B_33) | ~m1_subset_1(D_39, k1_zfmisc_1(u1_struct_0(B_33))) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(B_33) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.64/2.40  tff(c_1668, plain, (![C_211, A_212]: (~m1_subset_1(C_211, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212) | ~v2_pre_topc(A_212))), inference(splitLeft, [status(thm)], [c_30])).
% 6.64/2.40  tff(c_1674, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1286, c_1668])).
% 6.64/2.40  tff(c_1690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1674])).
% 6.64/2.40  tff(c_1692, plain, (![B_213, D_214]: (k1_tops_1(B_213, D_214)=D_214 | ~v3_pre_topc(D_214, B_213) | ~m1_subset_1(D_214, k1_zfmisc_1(u1_struct_0(B_213))) | ~l1_pre_topc(B_213))), inference(splitRight, [status(thm)], [c_30])).
% 6.64/2.40  tff(c_1704, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1692])).
% 6.64/2.40  tff(c_1717, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_778, c_1704])).
% 6.64/2.40  tff(c_784, plain, (![A_137, B_138]: (r1_tarski(k1_tops_1(A_137, B_138), B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.64/2.40  tff(c_786, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_784])).
% 6.64/2.40  tff(c_791, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_786])).
% 6.64/2.40  tff(c_797, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_791, c_2])).
% 6.64/2.40  tff(c_801, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_797])).
% 6.64/2.40  tff(c_1725, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1717, c_801])).
% 6.64/2.40  tff(c_1731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1725])).
% 6.64/2.40  tff(c_1732, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_797])).
% 6.64/2.40  tff(c_2073, plain, (![B_254, A_255]: (r1_tarski(B_254, k2_pre_topc(A_255, k1_tops_1(A_255, B_254))) | ~v4_tops_1(B_254, A_255) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.64/2.40  tff(c_2084, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1732, c_2073])).
% 6.64/2.40  tff(c_2091, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_783, c_2084])).
% 6.64/2.40  tff(c_2119, plain, (![A_258, B_259, C_260]: (r1_tarski(k1_tops_1(A_258, B_259), k1_tops_1(A_258, C_260)) | ~r1_tarski(B_259, C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(u1_struct_0(A_258))) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.64/2.40  tff(c_2142, plain, (![C_260]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_260)) | ~r1_tarski('#skF_4', C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1732, c_2119])).
% 6.64/2.40  tff(c_2191, plain, (![C_263]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_263)) | ~r1_tarski('#skF_4', C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_2142])).
% 6.64/2.40  tff(c_2195, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_2191])).
% 6.64/2.40  tff(c_2201, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2195])).
% 6.64/2.40  tff(c_2060, plain, (![A_252, B_253]: (r1_tarski(k1_tops_1(A_252, k2_pre_topc(A_252, B_253)), B_253) | ~v4_tops_1(B_253, A_252) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.64/2.40  tff(c_3088, plain, (![A_320, B_321]: (k1_tops_1(A_320, k2_pre_topc(A_320, B_321))=B_321 | ~r1_tarski(B_321, k1_tops_1(A_320, k2_pre_topc(A_320, B_321))) | ~v4_tops_1(B_321, A_320) | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(A_320))) | ~l1_pre_topc(A_320))), inference(resolution, [status(thm)], [c_2060, c_2])).
% 6.64/2.40  tff(c_3096, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2201, c_3088])).
% 6.64/2.40  tff(c_3113, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2091, c_36, c_783, c_3096])).
% 6.64/2.40  tff(c_16, plain, (![B_10, A_8]: (v6_tops_1(B_10, A_8) | k1_tops_1(A_8, k2_pre_topc(A_8, B_10))!=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.40  tff(c_3168, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3113, c_16])).
% 6.64/2.40  tff(c_3195, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_3168])).
% 6.64/2.40  tff(c_3197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_3195])).
% 6.64/2.40  tff(c_3199, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 6.64/2.40  tff(c_50, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_3200, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 6.64/2.40  tff(c_3201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3199, c_3200])).
% 6.64/2.40  tff(c_3202, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 6.64/2.40  tff(c_3198, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 6.64/2.40  tff(c_3544, plain, (![C_359, A_360]: (~m1_subset_1(C_359, k1_zfmisc_1(u1_struct_0(A_360))) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360))), inference(splitLeft, [status(thm)], [c_30])).
% 6.64/2.40  tff(c_3556, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_3544])).
% 6.64/2.40  tff(c_3567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3556])).
% 6.64/2.40  tff(c_3569, plain, (![B_361, D_362]: (k1_tops_1(B_361, D_362)=D_362 | ~v3_pre_topc(D_362, B_361) | ~m1_subset_1(D_362, k1_zfmisc_1(u1_struct_0(B_361))) | ~l1_pre_topc(B_361))), inference(splitRight, [status(thm)], [c_30])).
% 6.64/2.40  tff(c_3578, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_3569])).
% 6.64/2.40  tff(c_3588, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3198, c_3578])).
% 6.64/2.40  tff(c_3213, plain, (![A_324, B_325]: (r1_tarski(k1_tops_1(A_324, B_325), B_325) | ~m1_subset_1(B_325, k1_zfmisc_1(u1_struct_0(A_324))) | ~l1_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.64/2.40  tff(c_3215, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_3213])).
% 6.64/2.40  tff(c_3220, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3215])).
% 6.64/2.40  tff(c_3226, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_3220, c_2])).
% 6.64/2.40  tff(c_3230, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3226])).
% 6.64/2.40  tff(c_3597, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3588, c_3230])).
% 6.64/2.40  tff(c_3603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3597])).
% 6.64/2.40  tff(c_3604, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3226])).
% 6.64/2.40  tff(c_3674, plain, (![B_379, A_380]: (r1_tarski(B_379, k2_pre_topc(A_380, k1_tops_1(A_380, B_379))) | ~v4_tops_1(B_379, A_380) | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0(A_380))) | ~l1_pre_topc(A_380))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.64/2.40  tff(c_3682, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3604, c_3674])).
% 6.64/2.40  tff(c_3687, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_3202, c_3682])).
% 6.64/2.40  tff(c_3725, plain, (![A_383, B_384, C_385]: (r1_tarski(k1_tops_1(A_383, B_384), k1_tops_1(A_383, C_385)) | ~r1_tarski(B_384, C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(u1_struct_0(A_383))) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0(A_383))) | ~l1_pre_topc(A_383))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.64/2.40  tff(c_3748, plain, (![C_385]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_385)) | ~r1_tarski('#skF_4', C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3604, c_3725])).
% 6.64/2.40  tff(c_3769, plain, (![C_386]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_386)) | ~r1_tarski('#skF_4', C_386) | ~m1_subset_1(C_386, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_3748])).
% 6.64/2.40  tff(c_3773, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_3769])).
% 6.64/2.40  tff(c_3779, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3773])).
% 6.64/2.40  tff(c_3670, plain, (![A_377, B_378]: (r1_tarski(k1_tops_1(A_377, k2_pre_topc(A_377, B_378)), B_378) | ~v4_tops_1(B_378, A_377) | ~m1_subset_1(B_378, k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.64/2.40  tff(c_3908, plain, (![A_404, B_405]: (k1_tops_1(A_404, k2_pre_topc(A_404, B_405))=B_405 | ~r1_tarski(B_405, k1_tops_1(A_404, k2_pre_topc(A_404, B_405))) | ~v4_tops_1(B_405, A_404) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_3670, c_2])).
% 6.64/2.40  tff(c_3912, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3779, c_3908])).
% 6.64/2.40  tff(c_3919, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3687, c_36, c_3202, c_3912])).
% 6.64/2.40  tff(c_3952, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3919, c_16])).
% 6.64/2.40  tff(c_3975, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_3952])).
% 6.64/2.40  tff(c_3977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_3975])).
% 6.64/2.40  tff(c_3978, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 6.64/2.40  tff(c_4052, plain, (![A_416, B_417]: (k1_tops_1(A_416, k2_pre_topc(A_416, B_417))=B_417 | ~v6_tops_1(B_417, A_416) | ~m1_subset_1(B_417, k1_zfmisc_1(u1_struct_0(A_416))) | ~l1_pre_topc(A_416))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.40  tff(c_4058, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4052])).
% 6.64/2.40  tff(c_4065, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3978, c_4058])).
% 6.64/2.40  tff(c_4023, plain, (![A_412, B_413]: (m1_subset_1(k2_pre_topc(A_412, B_413), k1_zfmisc_1(u1_struct_0(A_412))) | ~m1_subset_1(B_413, k1_zfmisc_1(u1_struct_0(A_412))) | ~l1_pre_topc(A_412))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.64/2.40  tff(c_4121, plain, (![A_424, B_425]: (v3_pre_topc(k1_tops_1(A_424, k2_pre_topc(A_424, B_425)), A_424) | ~v2_pre_topc(A_424) | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0(A_424))) | ~l1_pre_topc(A_424))), inference(resolution, [status(thm)], [c_4023, c_20])).
% 6.64/2.40  tff(c_4124, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4065, c_4121])).
% 6.64/2.40  tff(c_4129, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_40, c_4124])).
% 6.64/2.40  tff(c_4131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3989, c_4129])).
% 6.64/2.40  tff(c_4133, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 6.64/2.40  tff(c_4132, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 6.64/2.40  tff(c_4134, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_4132])).
% 6.64/2.40  tff(c_4857, plain, (![A_490, B_491]: (k1_tops_1(A_490, k2_pre_topc(A_490, B_491))=B_491 | ~v6_tops_1(B_491, A_490) | ~m1_subset_1(B_491, k1_zfmisc_1(u1_struct_0(A_490))) | ~l1_pre_topc(A_490))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.40  tff(c_4863, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4857])).
% 6.64/2.40  tff(c_4870, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3978, c_4863])).
% 6.64/2.40  tff(c_4821, plain, (![A_482, B_483]: (m1_subset_1(k2_pre_topc(A_482, B_483), k1_zfmisc_1(u1_struct_0(A_482))) | ~m1_subset_1(B_483, k1_zfmisc_1(u1_struct_0(A_482))) | ~l1_pre_topc(A_482))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.64/2.40  tff(c_4903, plain, (![A_494, B_495]: (r1_tarski(k1_tops_1(A_494, k2_pre_topc(A_494, B_495)), k2_pre_topc(A_494, B_495)) | ~m1_subset_1(B_495, k1_zfmisc_1(u1_struct_0(A_494))) | ~l1_pre_topc(A_494))), inference(resolution, [status(thm)], [c_4821, c_24])).
% 6.64/2.40  tff(c_4908, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4870, c_4903])).
% 6.64/2.40  tff(c_4914, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_4908])).
% 6.64/2.40  tff(c_4415, plain, (![A_459, B_460]: (k1_tops_1(A_459, k2_pre_topc(A_459, B_460))=B_460 | ~v6_tops_1(B_460, A_459) | ~m1_subset_1(B_460, k1_zfmisc_1(u1_struct_0(A_459))) | ~l1_pre_topc(A_459))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.40  tff(c_4421, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4415])).
% 6.64/2.40  tff(c_4428, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3978, c_4421])).
% 6.64/2.40  tff(c_4139, plain, (![A_426, B_427]: (r1_tarski(k1_tops_1(A_426, B_427), B_427) | ~m1_subset_1(B_427, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_pre_topc(A_426))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.64/2.40  tff(c_4143, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4139])).
% 6.64/2.40  tff(c_4149, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4143])).
% 6.64/2.40  tff(c_4155, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_4149, c_2])).
% 6.64/2.40  tff(c_4375, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4155])).
% 6.64/2.40  tff(c_4395, plain, (![A_455, B_456]: (k1_tops_1(A_455, k1_tops_1(A_455, B_456))=k1_tops_1(A_455, B_456) | ~m1_subset_1(B_456, k1_zfmisc_1(u1_struct_0(A_455))) | ~l1_pre_topc(A_455))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.64/2.40  tff(c_4520, plain, (![A_469, B_470]: (k1_tops_1(A_469, k1_tops_1(A_469, k2_pre_topc(A_469, B_470)))=k1_tops_1(A_469, k2_pre_topc(A_469, B_470)) | ~m1_subset_1(B_470, k1_zfmisc_1(u1_struct_0(A_469))) | ~l1_pre_topc(A_469))), inference(resolution, [status(thm)], [c_8, c_4395])).
% 6.64/2.40  tff(c_4526, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4520])).
% 6.64/2.40  tff(c_4533, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4428, c_4428, c_4526])).
% 6.64/2.40  tff(c_4401, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4395])).
% 6.64/2.40  tff(c_4408, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4401])).
% 6.64/2.40  tff(c_4472, plain, (![B_465, A_466]: (r1_tarski(B_465, k2_pre_topc(A_466, k1_tops_1(A_466, B_465))) | ~v4_tops_1(B_465, A_466) | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0(A_466))) | ~l1_pre_topc(A_466))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.64/2.40  tff(c_4483, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4408, c_4472])).
% 6.64/2.40  tff(c_4493, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4483])).
% 6.64/2.40  tff(c_4503, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_4493])).
% 6.64/2.40  tff(c_4534, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_4503])).
% 6.64/2.40  tff(c_4541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_4534])).
% 6.64/2.40  tff(c_4543, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_4493])).
% 6.64/2.40  tff(c_4646, plain, (![A_475, B_476, C_477]: (r1_tarski(k1_tops_1(A_475, B_476), k1_tops_1(A_475, C_477)) | ~r1_tarski(B_476, C_477) | ~m1_subset_1(C_477, k1_zfmisc_1(u1_struct_0(A_475))) | ~m1_subset_1(B_476, k1_zfmisc_1(u1_struct_0(A_475))) | ~l1_pre_topc(A_475))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.64/2.40  tff(c_4672, plain, (![B_476]: (r1_tarski(k1_tops_1('#skF_1', B_476), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_476, k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_476, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4408, c_4646])).
% 6.64/2.40  tff(c_4746, plain, (![B_481]: (r1_tarski(k1_tops_1('#skF_1', B_481), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_481, k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(B_481, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4543, c_4672])).
% 6.64/2.40  tff(c_4754, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4428, c_4746])).
% 6.64/2.40  tff(c_4760, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_4375, c_4754])).
% 6.64/2.40  tff(c_4763, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_4760])).
% 6.64/2.40  tff(c_4766, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_4763])).
% 6.64/2.40  tff(c_4770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_4766])).
% 6.64/2.40  tff(c_4772, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_4760])).
% 6.64/2.40  tff(c_22, plain, (![A_13, B_14]: (k1_tops_1(A_13, k1_tops_1(A_13, B_14))=k1_tops_1(A_13, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.64/2.40  tff(c_4776, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4772, c_22])).
% 6.64/2.40  tff(c_4786, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4428, c_4428, c_4776])).
% 6.64/2.40  tff(c_4803, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4786, c_4375])).
% 6.64/2.40  tff(c_4812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4803])).
% 6.64/2.40  tff(c_4813, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_4155])).
% 6.64/2.40  tff(c_4974, plain, (![A_502, B_503, C_504]: (r1_tarski(k1_tops_1(A_502, B_503), k1_tops_1(A_502, C_504)) | ~r1_tarski(B_503, C_504) | ~m1_subset_1(C_504, k1_zfmisc_1(u1_struct_0(A_502))) | ~m1_subset_1(B_503, k1_zfmisc_1(u1_struct_0(A_502))) | ~l1_pre_topc(A_502))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.64/2.40  tff(c_4979, plain, (![C_504]: (r1_tarski('#skF_3', k1_tops_1('#skF_1', C_504)) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), C_504) | ~m1_subset_1(C_504, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4870, c_4974])).
% 6.64/2.40  tff(c_5003, plain, (![C_504]: (r1_tarski('#skF_3', k1_tops_1('#skF_1', C_504)) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), C_504) | ~m1_subset_1(C_504, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4979])).
% 6.64/2.40  tff(c_5032, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_5003])).
% 6.64/2.40  tff(c_5035, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_5032])).
% 6.64/2.40  tff(c_5039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_5035])).
% 6.64/2.40  tff(c_5041, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_5003])).
% 6.64/2.40  tff(c_4982, plain, (![B_503]: (r1_tarski(k1_tops_1('#skF_1', B_503), '#skF_3') | ~r1_tarski(B_503, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_503, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4870, c_4974])).
% 6.64/2.40  tff(c_5005, plain, (![B_503]: (r1_tarski(k1_tops_1('#skF_1', B_503), '#skF_3') | ~r1_tarski(B_503, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_503, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4982])).
% 6.64/2.40  tff(c_5255, plain, (![B_515]: (r1_tarski(k1_tops_1('#skF_1', B_515), '#skF_3') | ~r1_tarski(B_515, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(B_515, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_5041, c_5005])).
% 6.64/2.40  tff(c_5262, plain, (![B_4]: (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', B_4)), '#skF_3') | ~r1_tarski(k2_pre_topc('#skF_1', B_4), k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_5255])).
% 6.64/2.40  tff(c_5271, plain, (![B_4]: (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', B_4)), '#skF_3') | ~r1_tarski(k2_pre_topc('#skF_1', B_4), k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5262])).
% 6.64/2.40  tff(c_5435, plain, (![B_526, A_527]: (v4_tops_1(B_526, A_527) | ~r1_tarski(B_526, k2_pre_topc(A_527, k1_tops_1(A_527, B_526))) | ~r1_tarski(k1_tops_1(A_527, k2_pre_topc(A_527, B_526)), B_526) | ~m1_subset_1(B_526, k1_zfmisc_1(u1_struct_0(A_527))) | ~l1_pre_topc(A_527))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.64/2.40  tff(c_5439, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_5271, c_5435])).
% 6.64/2.40  tff(c_5463, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6, c_38, c_4914, c_4813, c_5439])).
% 6.64/2.40  tff(c_5465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4134, c_5463])).
% 6.64/2.40  tff(c_5467, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_4132])).
% 6.64/2.40  tff(c_3979, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.64/2.40  tff(c_42, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.64/2.40  tff(c_5471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4133, c_5467, c_3979, c_42])).
% 6.64/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.40  
% 6.64/2.40  Inference rules
% 6.64/2.40  ----------------------
% 6.64/2.40  #Ref     : 0
% 6.64/2.40  #Sup     : 1051
% 6.64/2.40  #Fact    : 0
% 6.64/2.40  #Define  : 0
% 6.64/2.40  #Split   : 129
% 6.64/2.40  #Chain   : 0
% 6.64/2.40  #Close   : 0
% 6.64/2.40  
% 6.64/2.40  Ordering : KBO
% 6.64/2.40  
% 6.64/2.40  Simplification rules
% 6.64/2.40  ----------------------
% 6.64/2.40  #Subsume      : 216
% 6.64/2.40  #Demod        : 1659
% 6.64/2.40  #Tautology    : 403
% 6.64/2.40  #SimpNegUnit  : 20
% 6.64/2.40  #BackRed      : 94
% 6.64/2.40  
% 6.64/2.40  #Partial instantiations: 0
% 6.64/2.40  #Strategies tried      : 1
% 6.64/2.40  
% 6.64/2.40  Timing (in seconds)
% 6.64/2.40  ----------------------
% 6.64/2.40  Preprocessing        : 0.40
% 6.64/2.40  Parsing              : 0.24
% 6.64/2.40  CNF conversion       : 0.03
% 6.64/2.40  Main loop            : 1.11
% 6.64/2.40  Inferencing          : 0.37
% 6.64/2.40  Reduction            : 0.39
% 6.64/2.40  Demodulation         : 0.27
% 6.64/2.40  BG Simplification    : 0.04
% 6.64/2.40  Subsumption          : 0.22
% 6.64/2.40  Abstraction          : 0.05
% 6.64/2.40  MUC search           : 0.00
% 6.64/2.40  Cooper               : 0.00
% 6.64/2.40  Total                : 1.59
% 6.64/2.40  Index Insertion      : 0.00
% 6.64/2.40  Index Deletion       : 0.00
% 6.64/2.40  Index Matching       : 0.00
% 6.64/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
