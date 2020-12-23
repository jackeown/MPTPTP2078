%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:23 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 274 expanded)
%              Number of leaves         :   27 ( 107 expanded)
%              Depth                    :    8
%              Number of atoms          :  302 (1143 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v4_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v5_tops_1(D,B) )
                      & ( v5_tops_1(C,A)
                       => ( v4_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(c_44,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1150,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_53,plain,(
    ~ v5_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_64,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_122,plain,(
    ! [A_50,B_51] :
      ( k2_pre_topc(A_50,k1_tops_1(A_50,B_51)) = B_51
      | ~ v5_tops_1(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_126,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_122])).

tff(c_132,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_126])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k1_tops_1(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_106,plain,(
    ! [A_46,B_47] :
      ( v4_pre_topc(k2_pre_topc(A_46,B_47),A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_164,plain,(
    ! [A_54,B_55] :
      ( v4_pre_topc(k2_pre_topc(A_54,k1_tops_1(A_54,B_55)),A_54)
      | ~ v2_pre_topc(A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_22,c_106])).

tff(c_167,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_164])).

tff(c_169,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_167])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_169])).

tff(c_172,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_176,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_179,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_181,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_186,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_181])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_239,plain,(
    ! [A_64,B_65] :
      ( k2_pre_topc(A_64,k1_tops_1(A_64,B_65)) = B_65
      | ~ v5_tops_1(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_243,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_239])).

tff(c_249,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_243])).

tff(c_173,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_193,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,B_59) = B_59
      | ~ v4_pre_topc(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_196,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_193])).

tff(c_202,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_173,c_196])).

tff(c_411,plain,(
    ! [B_94,A_95] :
      ( v4_tops_1(B_94,A_95)
      | ~ r1_tarski(B_94,k2_pre_topc(A_95,k1_tops_1(A_95,B_94)))
      | ~ r1_tarski(k1_tops_1(A_95,k2_pre_topc(A_95,B_94)),B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_420,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_411])).

tff(c_425,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_186,c_6,c_249,c_420])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_425])).

tff(c_428,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_429,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_431,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_429,c_42])).

tff(c_432,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k1_tops_1(A_96,B_97),B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_436,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_432])).

tff(c_442,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_436])).

tff(c_608,plain,(
    ! [A_124,C_125,B_126] :
      ( r1_tarski(k2_pre_topc(A_124,C_125),B_126)
      | ~ r1_tarski(C_125,B_126)
      | ~ v4_pre_topc(B_126,A_124)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_719,plain,(
    ! [A_133,B_134,B_135] :
      ( r1_tarski(k2_pre_topc(A_133,k1_tops_1(A_133,B_134)),B_135)
      | ~ r1_tarski(k1_tops_1(A_133,B_134),B_135)
      | ~ v4_pre_topc(B_135,A_133)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_22,c_608])).

tff(c_548,plain,(
    ! [B_114,A_115] :
      ( r1_tarski(B_114,k2_pre_topc(A_115,k1_tops_1(A_115,B_114)))
      | ~ v4_tops_1(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_554,plain,(
    ! [A_115,B_114] :
      ( k2_pre_topc(A_115,k1_tops_1(A_115,B_114)) = B_114
      | ~ r1_tarski(k2_pre_topc(A_115,k1_tops_1(A_115,B_114)),B_114)
      | ~ v4_tops_1(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_548,c_2])).

tff(c_782,plain,(
    ! [A_140,B_141] :
      ( k2_pre_topc(A_140,k1_tops_1(A_140,B_141)) = B_141
      | ~ v4_tops_1(B_141,A_140)
      | ~ r1_tarski(k1_tops_1(A_140,B_141),B_141)
      | ~ v4_pre_topc(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_719,c_554])).

tff(c_788,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_442,c_782])).

tff(c_797,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_428,c_431,c_788])).

tff(c_18,plain,(
    ! [B_11,A_9] :
      ( v5_tops_1(B_11,A_9)
      | k2_pre_topc(A_9,k1_tops_1(A_9,B_11)) != B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_824,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_18])).

tff(c_843,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_824])).

tff(c_845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_843])).

tff(c_846,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_847,plain,(
    ~ v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_848,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_847,c_48])).

tff(c_858,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k1_tops_1(A_144,B_145),B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_862,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_858])).

tff(c_868,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_862])).

tff(c_984,plain,(
    ! [A_170,C_171,B_172] :
      ( r1_tarski(k2_pre_topc(A_170,C_171),B_172)
      | ~ r1_tarski(C_171,B_172)
      | ~ v4_pre_topc(B_172,A_170)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1066,plain,(
    ! [A_186,B_187,B_188] :
      ( r1_tarski(k2_pre_topc(A_186,k1_tops_1(A_186,B_187)),B_188)
      | ~ r1_tarski(k1_tops_1(A_186,B_187),B_188)
      | ~ v4_pre_topc(B_188,A_186)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186) ) ),
    inference(resolution,[status(thm)],[c_22,c_984])).

tff(c_964,plain,(
    ! [B_164,A_165] :
      ( r1_tarski(B_164,k2_pre_topc(A_165,k1_tops_1(A_165,B_164)))
      | ~ v4_tops_1(B_164,A_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_967,plain,(
    ! [A_165,B_164] :
      ( k2_pre_topc(A_165,k1_tops_1(A_165,B_164)) = B_164
      | ~ r1_tarski(k2_pre_topc(A_165,k1_tops_1(A_165,B_164)),B_164)
      | ~ v4_tops_1(B_164,A_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(resolution,[status(thm)],[c_964,c_2])).

tff(c_1080,plain,(
    ! [A_189,B_190] :
      ( k2_pre_topc(A_189,k1_tops_1(A_189,B_190)) = B_190
      | ~ v4_tops_1(B_190,A_189)
      | ~ r1_tarski(k1_tops_1(A_189,B_190),B_190)
      | ~ v4_pre_topc(B_190,A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(resolution,[status(thm)],[c_1066,c_967])).

tff(c_1084,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_868,c_1080])).

tff(c_1090,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_846,c_848,c_1084])).

tff(c_1117,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_18])).

tff(c_1136,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1117])).

tff(c_1138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1136])).

tff(c_1139,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1209,plain,(
    ! [A_201,B_202] :
      ( k2_pre_topc(A_201,k1_tops_1(A_201,B_202)) = B_202
      | ~ v5_tops_1(B_202,A_201)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1213,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1209])).

tff(c_1219,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1139,c_1213])).

tff(c_1197,plain,(
    ! [A_199,B_200] :
      ( m1_subset_1(k1_tops_1(A_199,B_200),k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( v4_pre_topc(k2_pre_topc(A_14,B_15),A_14)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1279,plain,(
    ! [A_211,B_212] :
      ( v4_pre_topc(k2_pre_topc(A_211,k1_tops_1(A_211,B_212)),A_211)
      | ~ v2_pre_topc(A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(resolution,[status(thm)],[c_1197,c_24])).

tff(c_1285,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_1279])).

tff(c_1290,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_1285])).

tff(c_1292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1150,c_1290])).

tff(c_1294,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1293,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1295,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1293])).

tff(c_1301,plain,(
    ! [A_213,B_214] :
      ( r1_tarski(k1_tops_1(A_213,B_214),B_214)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1303,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1301])).

tff(c_1308,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1303])).

tff(c_1364,plain,(
    ! [A_223,B_224] :
      ( k2_pre_topc(A_223,k1_tops_1(A_223,B_224)) = B_224
      | ~ v5_tops_1(B_224,A_223)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1368,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1364])).

tff(c_1374,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1139,c_1368])).

tff(c_1339,plain,(
    ! [A_219,B_220] :
      ( k2_pre_topc(A_219,B_220) = B_220
      | ~ v4_pre_topc(B_220,A_219)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1345,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1339])).

tff(c_1352,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1294,c_1345])).

tff(c_1521,plain,(
    ! [B_245,A_246] :
      ( v4_tops_1(B_245,A_246)
      | ~ r1_tarski(B_245,k2_pre_topc(A_246,k1_tops_1(A_246,B_245)))
      | ~ r1_tarski(k1_tops_1(A_246,k2_pre_topc(A_246,B_245)),B_245)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1533,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1352,c_1521])).

tff(c_1540,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1308,c_6,c_1374,c_1533])).

tff(c_1542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1295,c_1540])).

tff(c_1544,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1293])).

tff(c_1140,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_1544,c_1140,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.61  
% 3.60/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.61  %$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.60/1.61  
% 3.60/1.61  %Foreground sorts:
% 3.60/1.61  
% 3.60/1.61  
% 3.60/1.61  %Background operators:
% 3.60/1.61  
% 3.60/1.61  
% 3.60/1.61  %Foreground operators:
% 3.60/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.60/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.61  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 3.60/1.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.60/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.61  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.60/1.61  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 3.60/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.60/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.60/1.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.60/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.61  
% 4.00/1.63  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v4_pre_topc(D, B) & v4_tops_1(D, B)) => v5_tops_1(D, B)) & (v5_tops_1(C, A) => (v4_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tops_1)).
% 4.00/1.63  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 4.00/1.63  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.00/1.63  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.00/1.63  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.00/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.00/1.63  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.00/1.63  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 4.00/1.63  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 4.00/1.63  tff(c_44, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_1150, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.00/1.63  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_46, plain, (~v5_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_53, plain, (~v5_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 4.00/1.63  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_64, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.00/1.63  tff(c_50, plain, (v4_pre_topc('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_54, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 4.00/1.63  tff(c_122, plain, (![A_50, B_51]: (k2_pre_topc(A_50, k1_tops_1(A_50, B_51))=B_51 | ~v5_tops_1(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.00/1.63  tff(c_126, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_122])).
% 4.00/1.63  tff(c_132, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_126])).
% 4.00/1.63  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(k1_tops_1(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.00/1.63  tff(c_106, plain, (![A_46, B_47]: (v4_pre_topc(k2_pre_topc(A_46, B_47), A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.00/1.63  tff(c_164, plain, (![A_54, B_55]: (v4_pre_topc(k2_pre_topc(A_54, k1_tops_1(A_54, B_55)), A_54) | ~v2_pre_topc(A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_22, c_106])).
% 4.00/1.63  tff(c_167, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_132, c_164])).
% 4.00/1.63  tff(c_169, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_167])).
% 4.00/1.63  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_169])).
% 4.00/1.63  tff(c_172, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.00/1.63  tff(c_176, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_172])).
% 4.00/1.63  tff(c_179, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.00/1.63  tff(c_181, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_179])).
% 4.00/1.63  tff(c_186, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_181])).
% 4.00/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.63  tff(c_239, plain, (![A_64, B_65]: (k2_pre_topc(A_64, k1_tops_1(A_64, B_65))=B_65 | ~v5_tops_1(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.00/1.63  tff(c_243, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_239])).
% 4.00/1.63  tff(c_249, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_243])).
% 4.00/1.63  tff(c_173, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.00/1.63  tff(c_193, plain, (![A_58, B_59]: (k2_pre_topc(A_58, B_59)=B_59 | ~v4_pre_topc(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.00/1.63  tff(c_196, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_193])).
% 4.00/1.63  tff(c_202, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_173, c_196])).
% 4.00/1.63  tff(c_411, plain, (![B_94, A_95]: (v4_tops_1(B_94, A_95) | ~r1_tarski(B_94, k2_pre_topc(A_95, k1_tops_1(A_95, B_94))) | ~r1_tarski(k1_tops_1(A_95, k2_pre_topc(A_95, B_94)), B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.00/1.63  tff(c_420, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_202, c_411])).
% 4.00/1.63  tff(c_425, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_186, c_6, c_249, c_420])).
% 4.00/1.63  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_425])).
% 4.00/1.63  tff(c_428, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_172])).
% 4.00/1.63  tff(c_429, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_172])).
% 4.00/1.63  tff(c_42, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_431, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_429, c_42])).
% 4.00/1.63  tff(c_432, plain, (![A_96, B_97]: (r1_tarski(k1_tops_1(A_96, B_97), B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.00/1.63  tff(c_436, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_432])).
% 4.00/1.63  tff(c_442, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_436])).
% 4.00/1.63  tff(c_608, plain, (![A_124, C_125, B_126]: (r1_tarski(k2_pre_topc(A_124, C_125), B_126) | ~r1_tarski(C_125, B_126) | ~v4_pre_topc(B_126, A_124) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.00/1.63  tff(c_719, plain, (![A_133, B_134, B_135]: (r1_tarski(k2_pre_topc(A_133, k1_tops_1(A_133, B_134)), B_135) | ~r1_tarski(k1_tops_1(A_133, B_134), B_135) | ~v4_pre_topc(B_135, A_133) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_22, c_608])).
% 4.00/1.63  tff(c_548, plain, (![B_114, A_115]: (r1_tarski(B_114, k2_pre_topc(A_115, k1_tops_1(A_115, B_114))) | ~v4_tops_1(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.00/1.63  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.63  tff(c_554, plain, (![A_115, B_114]: (k2_pre_topc(A_115, k1_tops_1(A_115, B_114))=B_114 | ~r1_tarski(k2_pre_topc(A_115, k1_tops_1(A_115, B_114)), B_114) | ~v4_tops_1(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_548, c_2])).
% 4.00/1.63  tff(c_782, plain, (![A_140, B_141]: (k2_pre_topc(A_140, k1_tops_1(A_140, B_141))=B_141 | ~v4_tops_1(B_141, A_140) | ~r1_tarski(k1_tops_1(A_140, B_141), B_141) | ~v4_pre_topc(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_719, c_554])).
% 4.00/1.63  tff(c_788, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_442, c_782])).
% 4.00/1.63  tff(c_797, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_428, c_431, c_788])).
% 4.00/1.63  tff(c_18, plain, (![B_11, A_9]: (v5_tops_1(B_11, A_9) | k2_pre_topc(A_9, k1_tops_1(A_9, B_11))!=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.00/1.63  tff(c_824, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_797, c_18])).
% 4.00/1.63  tff(c_843, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_824])).
% 4.00/1.63  tff(c_845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_843])).
% 4.00/1.63  tff(c_846, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 4.00/1.63  tff(c_847, plain, (~v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.00/1.63  tff(c_48, plain, (v4_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_848, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_847, c_48])).
% 4.00/1.63  tff(c_858, plain, (![A_144, B_145]: (r1_tarski(k1_tops_1(A_144, B_145), B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.00/1.63  tff(c_862, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_858])).
% 4.00/1.63  tff(c_868, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_862])).
% 4.00/1.63  tff(c_984, plain, (![A_170, C_171, B_172]: (r1_tarski(k2_pre_topc(A_170, C_171), B_172) | ~r1_tarski(C_171, B_172) | ~v4_pre_topc(B_172, A_170) | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.00/1.63  tff(c_1066, plain, (![A_186, B_187, B_188]: (r1_tarski(k2_pre_topc(A_186, k1_tops_1(A_186, B_187)), B_188) | ~r1_tarski(k1_tops_1(A_186, B_187), B_188) | ~v4_pre_topc(B_188, A_186) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_186))) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186))), inference(resolution, [status(thm)], [c_22, c_984])).
% 4.00/1.63  tff(c_964, plain, (![B_164, A_165]: (r1_tarski(B_164, k2_pre_topc(A_165, k1_tops_1(A_165, B_164))) | ~v4_tops_1(B_164, A_165) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.00/1.63  tff(c_967, plain, (![A_165, B_164]: (k2_pre_topc(A_165, k1_tops_1(A_165, B_164))=B_164 | ~r1_tarski(k2_pre_topc(A_165, k1_tops_1(A_165, B_164)), B_164) | ~v4_tops_1(B_164, A_165) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(resolution, [status(thm)], [c_964, c_2])).
% 4.00/1.63  tff(c_1080, plain, (![A_189, B_190]: (k2_pre_topc(A_189, k1_tops_1(A_189, B_190))=B_190 | ~v4_tops_1(B_190, A_189) | ~r1_tarski(k1_tops_1(A_189, B_190), B_190) | ~v4_pre_topc(B_190, A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(resolution, [status(thm)], [c_1066, c_967])).
% 4.00/1.63  tff(c_1084, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_868, c_1080])).
% 4.00/1.63  tff(c_1090, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_846, c_848, c_1084])).
% 4.00/1.63  tff(c_1117, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1090, c_18])).
% 4.00/1.63  tff(c_1136, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1117])).
% 4.00/1.63  tff(c_1138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1136])).
% 4.00/1.63  tff(c_1139, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.00/1.63  tff(c_1209, plain, (![A_201, B_202]: (k2_pre_topc(A_201, k1_tops_1(A_201, B_202))=B_202 | ~v5_tops_1(B_202, A_201) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.00/1.63  tff(c_1213, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1209])).
% 4.00/1.63  tff(c_1219, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1139, c_1213])).
% 4.00/1.63  tff(c_1197, plain, (![A_199, B_200]: (m1_subset_1(k1_tops_1(A_199, B_200), k1_zfmisc_1(u1_struct_0(A_199))) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.00/1.63  tff(c_24, plain, (![A_14, B_15]: (v4_pre_topc(k2_pre_topc(A_14, B_15), A_14) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.00/1.63  tff(c_1279, plain, (![A_211, B_212]: (v4_pre_topc(k2_pre_topc(A_211, k1_tops_1(A_211, B_212)), A_211) | ~v2_pre_topc(A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_211))) | ~l1_pre_topc(A_211))), inference(resolution, [status(thm)], [c_1197, c_24])).
% 4.00/1.63  tff(c_1285, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1219, c_1279])).
% 4.00/1.63  tff(c_1290, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_1285])).
% 4.00/1.63  tff(c_1292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1150, c_1290])).
% 4.00/1.63  tff(c_1294, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.00/1.63  tff(c_1293, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.00/1.63  tff(c_1295, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1293])).
% 4.00/1.63  tff(c_1301, plain, (![A_213, B_214]: (r1_tarski(k1_tops_1(A_213, B_214), B_214) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.00/1.63  tff(c_1303, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1301])).
% 4.00/1.63  tff(c_1308, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1303])).
% 4.00/1.63  tff(c_1364, plain, (![A_223, B_224]: (k2_pre_topc(A_223, k1_tops_1(A_223, B_224))=B_224 | ~v5_tops_1(B_224, A_223) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.00/1.63  tff(c_1368, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1364])).
% 4.00/1.63  tff(c_1374, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1139, c_1368])).
% 4.00/1.63  tff(c_1339, plain, (![A_219, B_220]: (k2_pre_topc(A_219, B_220)=B_220 | ~v4_pre_topc(B_220, A_219) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.00/1.63  tff(c_1345, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1339])).
% 4.00/1.63  tff(c_1352, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1294, c_1345])).
% 4.00/1.63  tff(c_1521, plain, (![B_245, A_246]: (v4_tops_1(B_245, A_246) | ~r1_tarski(B_245, k2_pre_topc(A_246, k1_tops_1(A_246, B_245))) | ~r1_tarski(k1_tops_1(A_246, k2_pre_topc(A_246, B_245)), B_245) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.00/1.63  tff(c_1533, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1352, c_1521])).
% 4.00/1.63  tff(c_1540, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1308, c_6, c_1374, c_1533])).
% 4.00/1.63  tff(c_1542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1295, c_1540])).
% 4.00/1.63  tff(c_1544, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1293])).
% 4.00/1.63  tff(c_1140, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.00/1.63  tff(c_40, plain, (~v5_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.00/1.63  tff(c_1546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1294, c_1544, c_1140, c_40])).
% 4.00/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.63  
% 4.00/1.63  Inference rules
% 4.00/1.63  ----------------------
% 4.00/1.63  #Ref     : 0
% 4.00/1.63  #Sup     : 290
% 4.00/1.63  #Fact    : 0
% 4.00/1.63  #Define  : 0
% 4.00/1.63  #Split   : 46
% 4.00/1.63  #Chain   : 0
% 4.00/1.63  #Close   : 0
% 4.00/1.63  
% 4.00/1.63  Ordering : KBO
% 4.00/1.63  
% 4.00/1.63  Simplification rules
% 4.00/1.63  ----------------------
% 4.00/1.63  #Subsume      : 45
% 4.00/1.63  #Demod        : 412
% 4.00/1.63  #Tautology    : 92
% 4.00/1.63  #SimpNegUnit  : 21
% 4.00/1.63  #BackRed      : 2
% 4.00/1.63  
% 4.00/1.63  #Partial instantiations: 0
% 4.00/1.63  #Strategies tried      : 1
% 4.00/1.63  
% 4.00/1.63  Timing (in seconds)
% 4.00/1.63  ----------------------
% 4.00/1.64  Preprocessing        : 0.31
% 4.00/1.64  Parsing              : 0.18
% 4.00/1.64  CNF conversion       : 0.02
% 4.00/1.64  Main loop            : 0.55
% 4.00/1.64  Inferencing          : 0.19
% 4.00/1.64  Reduction            : 0.18
% 4.00/1.64  Demodulation         : 0.12
% 4.00/1.64  BG Simplification    : 0.02
% 4.00/1.64  Subsumption          : 0.11
% 4.00/1.64  Abstraction          : 0.03
% 4.00/1.64  MUC search           : 0.00
% 4.00/1.64  Cooper               : 0.00
% 4.00/1.64  Total                : 0.91
% 4.00/1.64  Index Insertion      : 0.00
% 4.00/1.64  Index Deletion       : 0.00
% 4.00/1.64  Index Matching       : 0.00
% 4.00/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
