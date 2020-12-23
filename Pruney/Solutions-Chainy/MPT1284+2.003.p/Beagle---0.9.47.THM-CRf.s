%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:23 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 450 expanded)
%              Number of leaves         :   27 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  369 (1820 expanded)
%              Number of equality atoms :   42 (  92 expanded)
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

tff(f_131,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(c_46,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1791,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_55,plain,(
    ~ v5_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_66,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_56,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_145,plain,(
    ! [A_52,B_53] :
      ( k2_pre_topc(A_52,k1_tops_1(A_52,B_53)) = B_53
      | ~ v5_tops_1(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_151,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_145])).

tff(c_158,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_151])).

tff(c_112,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k1_tops_1(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( v4_pre_topc(k2_pre_topc(A_26,B_27),A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_201,plain,(
    ! [A_60,B_61] :
      ( v4_pre_topc(k2_pre_topc(A_60,k1_tops_1(A_60,B_61)),A_60)
      | ~ v2_pre_topc(A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_112,c_30])).

tff(c_204,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_201])).

tff(c_206,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_40,c_204])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_206])).

tff(c_210,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_209,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_211,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_339,plain,(
    ! [A_78,B_79] :
      ( k2_pre_topc(A_78,k1_tops_1(A_78,B_79)) = B_79
      | ~ v5_tops_1(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_345,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_339])).

tff(c_352,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_345])).

tff(c_291,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k1_tops_1(A_70,B_71),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [B_7,A_5] :
      ( r1_tarski(B_7,k2_pre_topc(A_5,B_7))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_377,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k1_tops_1(A_84,B_85),k2_pre_topc(A_84,k1_tops_1(A_84,B_85)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_291,c_10])).

tff(c_382,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_377])).

tff(c_385,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_382])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_247,plain,(
    ! [A_66,B_67] :
      ( k2_pre_topc(A_66,B_67) = B_67
      | ~ v4_pre_topc(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_253,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_247])).

tff(c_259,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_210,c_253])).

tff(c_216,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,k2_pre_topc(A_63,B_62))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_220,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_216])).

tff(c_226,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_220])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_232,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_246,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_260,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_246])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_260])).

tff(c_266,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_539,plain,(
    ! [B_101,A_102] :
      ( v4_tops_1(B_101,A_102)
      | ~ r1_tarski(B_101,k2_pre_topc(A_102,k1_tops_1(A_102,B_101)))
      | ~ r1_tarski(k1_tops_1(A_102,k2_pre_topc(A_102,B_101)),B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_554,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_539])).

tff(c_563,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_385,c_6,c_352,c_554])).

tff(c_565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_563])).

tff(c_567,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_44,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_569,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_567,c_44])).

tff(c_566,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_603,plain,(
    ! [A_107,B_108] :
      ( k2_pre_topc(A_107,B_108) = B_108
      | ~ v4_pre_topc(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_606,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_603])).

tff(c_612,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_566,c_606])).

tff(c_572,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(B_103,k2_pre_topc(A_104,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_574,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_572])).

tff(c_579,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_574])).

tff(c_585,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_579,c_2])).

tff(c_589,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_616,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_589])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_616])).

tff(c_621,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_775,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(k1_tops_1(A_129,k2_pre_topc(A_129,B_130)),B_130)
      | ~ v4_tops_1(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_786,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_775])).

tff(c_793,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_569,c_786])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k1_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_837,plain,(
    ! [A_139,B_140,C_141] :
      ( r1_tarski(k2_pre_topc(A_139,B_140),k2_pre_topc(A_139,C_141))
      | ~ r1_tarski(B_140,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_863,plain,(
    ! [B_140] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_140),'#skF_4')
      | ~ r1_tarski(B_140,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_837])).

tff(c_1028,plain,(
    ! [B_149] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_149),'#skF_4')
      | ~ r1_tarski(B_149,'#skF_4')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_863])).

tff(c_1032,plain,(
    ! [B_25] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_25)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_25),'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_1028])).

tff(c_1038,plain,(
    ! [B_25] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_25)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_25),'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1032])).

tff(c_798,plain,(
    ! [B_131,A_132] :
      ( r1_tarski(B_131,k2_pre_topc(A_132,k1_tops_1(A_132,B_131)))
      | ~ v4_tops_1(B_131,A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1250,plain,(
    ! [A_164,B_165] :
      ( k2_pre_topc(A_164,k1_tops_1(A_164,B_165)) = B_165
      | ~ r1_tarski(k2_pre_topc(A_164,k1_tops_1(A_164,B_165)),B_165)
      | ~ v4_tops_1(B_165,A_164)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_798,c_2])).

tff(c_1262,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1038,c_1250])).

tff(c_1278,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_793,c_36,c_569,c_1262])).

tff(c_24,plain,(
    ! [B_23,A_21] :
      ( v5_tops_1(B_23,A_21)
      | k2_pre_topc(A_21,k1_tops_1(A_21,B_23)) != B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1319,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_24])).

tff(c_1346,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1319])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_1346])).

tff(c_1350,plain,(
    ~ v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1351,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1350,c_50])).

tff(c_1349,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1399,plain,(
    ! [A_174,B_175] :
      ( k2_pre_topc(A_174,B_175) = B_175
      | ~ v4_pre_topc(B_175,A_174)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1405,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1399])).

tff(c_1412,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1349,c_1405])).

tff(c_1361,plain,(
    ! [B_168,A_169] :
      ( r1_tarski(B_168,k2_pre_topc(A_169,B_168))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1363,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1361])).

tff(c_1368,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1363])).

tff(c_1385,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1368,c_2])).

tff(c_1390,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1385])).

tff(c_1416,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_1390])).

tff(c_1420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1416])).

tff(c_1421,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_1512,plain,(
    ! [A_192,B_193] :
      ( r1_tarski(k1_tops_1(A_192,k2_pre_topc(A_192,B_193)),B_193)
      | ~ v4_tops_1(B_193,A_192)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1520,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_1512])).

tff(c_1525,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1351,c_1520])).

tff(c_1568,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_tarski(k2_pre_topc(A_200,B_201),k2_pre_topc(A_200,C_202))
      | ~ r1_tarski(B_201,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1594,plain,(
    ! [B_201] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_201),'#skF_4')
      | ~ r1_tarski(B_201,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_1568])).

tff(c_1626,plain,(
    ! [B_204] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_204),'#skF_4')
      | ~ r1_tarski(B_204,'#skF_4')
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1594])).

tff(c_1630,plain,(
    ! [B_25] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_25)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_25),'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_1626])).

tff(c_1636,plain,(
    ! [B_25] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_25)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_25),'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1630])).

tff(c_1526,plain,(
    ! [B_194,A_195] :
      ( r1_tarski(B_194,k2_pre_topc(A_195,k1_tops_1(A_195,B_194)))
      | ~ v4_tops_1(B_194,A_195)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1705,plain,(
    ! [A_213,B_214] :
      ( k2_pre_topc(A_213,k1_tops_1(A_213,B_214)) = B_214
      | ~ r1_tarski(k2_pre_topc(A_213,k1_tops_1(A_213,B_214)),B_214)
      | ~ v4_tops_1(B_214,A_213)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(resolution,[status(thm)],[c_1526,c_2])).

tff(c_1709,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1636,c_1705])).

tff(c_1716,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1525,c_36,c_1351,c_1709])).

tff(c_1752,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1716,c_24])).

tff(c_1777,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1752])).

tff(c_1779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_1777])).

tff(c_1780,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1874,plain,(
    ! [A_229,B_230] :
      ( k2_pre_topc(A_229,k1_tops_1(A_229,B_230)) = B_230
      | ~ v5_tops_1(B_230,A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1880,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1874])).

tff(c_1887,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1780,c_1880])).

tff(c_1839,plain,(
    ! [A_223,B_224] :
      ( m1_subset_1(k1_tops_1(A_223,B_224),k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1925,plain,(
    ! [A_233,B_234] :
      ( v4_pre_topc(k2_pre_topc(A_233,k1_tops_1(A_233,B_234)),A_233)
      | ~ v2_pre_topc(A_233)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_1839,c_30])).

tff(c_1928,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1887,c_1925])).

tff(c_1933,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_40,c_1928])).

tff(c_1935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1791,c_1933])).

tff(c_1937,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1781,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1939,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_1781,c_42])).

tff(c_2231,plain,(
    ! [A_271,B_272] :
      ( k2_pre_topc(A_271,k1_tops_1(A_271,B_272)) = B_272
      | ~ v5_tops_1(B_272,A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2237,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_2231])).

tff(c_2244,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1780,c_2237])).

tff(c_2168,plain,(
    ! [A_261,B_262] :
      ( m1_subset_1(k1_tops_1(A_261,B_262),k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2289,plain,(
    ! [A_277,B_278] :
      ( r1_tarski(k1_tops_1(A_277,B_278),k2_pre_topc(A_277,k1_tops_1(A_277,B_278)))
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_pre_topc(A_277) ) ),
    inference(resolution,[status(thm)],[c_2168,c_10])).

tff(c_2294,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_2289])).

tff(c_2300,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_2294])).

tff(c_1959,plain,(
    ! [A_237,B_238] :
      ( k2_pre_topc(A_237,B_238) = B_238
      | ~ v4_pre_topc(B_238,A_237)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1965,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1959])).

tff(c_1971,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1937,c_1965])).

tff(c_2468,plain,(
    ! [B_294,A_295] :
      ( v4_tops_1(B_294,A_295)
      | ~ r1_tarski(B_294,k2_pre_topc(A_295,k1_tops_1(A_295,B_294)))
      | ~ r1_tarski(k1_tops_1(A_295,k2_pre_topc(A_295,B_294)),B_294)
      | ~ m1_subset_1(B_294,k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2483,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1971,c_2468])).

tff(c_2492,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_2300,c_6,c_2244,c_2483])).

tff(c_2494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1939,c_2492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.88  
% 4.33/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.88  %$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.33/1.88  
% 4.33/1.88  %Foreground sorts:
% 4.33/1.88  
% 4.33/1.88  
% 4.33/1.88  %Background operators:
% 4.33/1.88  
% 4.33/1.88  
% 4.33/1.88  %Foreground operators:
% 4.33/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.33/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.88  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 4.33/1.88  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.33/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.33/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.33/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.33/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.33/1.88  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.33/1.88  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 4.33/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.33/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.33/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.33/1.88  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.33/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.33/1.88  
% 4.33/1.90  tff(f_131, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v4_pre_topc(D, B) & v4_tops_1(D, B)) => v5_tops_1(D, B)) & (v5_tops_1(C, A) => (v4_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tops_1)).
% 4.33/1.90  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 4.33/1.90  tff(f_97, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.33/1.90  tff(f_105, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.33/1.90  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.33/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.33/1.90  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.33/1.90  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 4.33/1.90  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 4.33/1.90  tff(c_46, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.90  tff(c_1791, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.33/1.90  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.90  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.90  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.90  tff(c_48, plain, (~v5_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.90  tff(c_55, plain, (~v5_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 4.33/1.90  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.90  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.90  tff(c_66, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.33/1.90  tff(c_52, plain, (v4_pre_topc('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.90  tff(c_56, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 4.33/1.90  tff(c_145, plain, (![A_52, B_53]: (k2_pre_topc(A_52, k1_tops_1(A_52, B_53))=B_53 | ~v5_tops_1(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.33/1.90  tff(c_151, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_145])).
% 4.33/1.90  tff(c_158, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_151])).
% 4.33/1.90  tff(c_112, plain, (![A_48, B_49]: (m1_subset_1(k1_tops_1(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.33/1.90  tff(c_30, plain, (![A_26, B_27]: (v4_pre_topc(k2_pre_topc(A_26, B_27), A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/1.90  tff(c_201, plain, (![A_60, B_61]: (v4_pre_topc(k2_pre_topc(A_60, k1_tops_1(A_60, B_61)), A_60) | ~v2_pre_topc(A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_112, c_30])).
% 4.33/1.90  tff(c_204, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_158, c_201])).
% 4.33/1.90  tff(c_206, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_40, c_204])).
% 4.33/1.90  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_206])).
% 4.33/1.90  tff(c_210, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.33/1.90  tff(c_209, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.33/1.90  tff(c_211, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_209])).
% 4.33/1.90  tff(c_339, plain, (![A_78, B_79]: (k2_pre_topc(A_78, k1_tops_1(A_78, B_79))=B_79 | ~v5_tops_1(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.33/1.90  tff(c_345, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_339])).
% 4.33/1.90  tff(c_352, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_345])).
% 4.33/1.90  tff(c_291, plain, (![A_70, B_71]: (m1_subset_1(k1_tops_1(A_70, B_71), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.33/1.90  tff(c_10, plain, (![B_7, A_5]: (r1_tarski(B_7, k2_pre_topc(A_5, B_7)) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.33/1.90  tff(c_377, plain, (![A_84, B_85]: (r1_tarski(k1_tops_1(A_84, B_85), k2_pre_topc(A_84, k1_tops_1(A_84, B_85))) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_291, c_10])).
% 4.33/1.90  tff(c_382, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_352, c_377])).
% 4.33/1.91  tff(c_385, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_382])).
% 4.33/1.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.33/1.91  tff(c_247, plain, (![A_66, B_67]: (k2_pre_topc(A_66, B_67)=B_67 | ~v4_pre_topc(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.33/1.91  tff(c_253, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_247])).
% 4.33/1.91  tff(c_259, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_210, c_253])).
% 4.33/1.91  tff(c_216, plain, (![B_62, A_63]: (r1_tarski(B_62, k2_pre_topc(A_63, B_62)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.33/1.91  tff(c_220, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_216])).
% 4.33/1.91  tff(c_226, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_220])).
% 4.33/1.91  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.33/1.91  tff(c_232, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_226, c_2])).
% 4.33/1.91  tff(c_246, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_232])).
% 4.33/1.91  tff(c_260, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_246])).
% 4.33/1.91  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_260])).
% 4.33/1.91  tff(c_266, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_232])).
% 4.33/1.91  tff(c_539, plain, (![B_101, A_102]: (v4_tops_1(B_101, A_102) | ~r1_tarski(B_101, k2_pre_topc(A_102, k1_tops_1(A_102, B_101))) | ~r1_tarski(k1_tops_1(A_102, k2_pre_topc(A_102, B_101)), B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.33/1.91  tff(c_554, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_266, c_539])).
% 4.33/1.91  tff(c_563, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_385, c_6, c_352, c_554])).
% 4.33/1.91  tff(c_565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_563])).
% 4.33/1.91  tff(c_567, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_209])).
% 4.33/1.91  tff(c_44, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.91  tff(c_569, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_567, c_44])).
% 4.33/1.91  tff(c_566, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_209])).
% 4.33/1.91  tff(c_603, plain, (![A_107, B_108]: (k2_pre_topc(A_107, B_108)=B_108 | ~v4_pre_topc(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.33/1.91  tff(c_606, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_603])).
% 4.33/1.91  tff(c_612, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_566, c_606])).
% 4.33/1.91  tff(c_572, plain, (![B_103, A_104]: (r1_tarski(B_103, k2_pre_topc(A_104, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.33/1.91  tff(c_574, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_572])).
% 4.33/1.91  tff(c_579, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_574])).
% 4.33/1.91  tff(c_585, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_579, c_2])).
% 4.33/1.91  tff(c_589, plain, (~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_585])).
% 4.33/1.91  tff(c_616, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_589])).
% 4.33/1.91  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_616])).
% 4.33/1.91  tff(c_621, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_585])).
% 4.33/1.91  tff(c_775, plain, (![A_129, B_130]: (r1_tarski(k1_tops_1(A_129, k2_pre_topc(A_129, B_130)), B_130) | ~v4_tops_1(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.33/1.91  tff(c_786, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_621, c_775])).
% 4.33/1.91  tff(c_793, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_569, c_786])).
% 4.33/1.91  tff(c_28, plain, (![A_24, B_25]: (m1_subset_1(k1_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.33/1.91  tff(c_837, plain, (![A_139, B_140, C_141]: (r1_tarski(k2_pre_topc(A_139, B_140), k2_pre_topc(A_139, C_141)) | ~r1_tarski(B_140, C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.33/1.91  tff(c_863, plain, (![B_140]: (r1_tarski(k2_pre_topc('#skF_2', B_140), '#skF_4') | ~r1_tarski(B_140, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_621, c_837])).
% 4.33/1.91  tff(c_1028, plain, (![B_149]: (r1_tarski(k2_pre_topc('#skF_2', B_149), '#skF_4') | ~r1_tarski(B_149, '#skF_4') | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_863])).
% 4.33/1.91  tff(c_1032, plain, (![B_25]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_25)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_25), '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_1028])).
% 4.33/1.91  tff(c_1038, plain, (![B_25]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_25)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_25), '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1032])).
% 4.33/1.91  tff(c_798, plain, (![B_131, A_132]: (r1_tarski(B_131, k2_pre_topc(A_132, k1_tops_1(A_132, B_131))) | ~v4_tops_1(B_131, A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.33/1.91  tff(c_1250, plain, (![A_164, B_165]: (k2_pre_topc(A_164, k1_tops_1(A_164, B_165))=B_165 | ~r1_tarski(k2_pre_topc(A_164, k1_tops_1(A_164, B_165)), B_165) | ~v4_tops_1(B_165, A_164) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_798, c_2])).
% 4.33/1.91  tff(c_1262, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1038, c_1250])).
% 4.33/1.91  tff(c_1278, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_793, c_36, c_569, c_1262])).
% 4.33/1.91  tff(c_24, plain, (![B_23, A_21]: (v5_tops_1(B_23, A_21) | k2_pre_topc(A_21, k1_tops_1(A_21, B_23))!=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.33/1.91  tff(c_1319, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1278, c_24])).
% 4.33/1.91  tff(c_1346, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1319])).
% 4.33/1.91  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_1346])).
% 4.33/1.91  tff(c_1350, plain, (~v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 4.33/1.91  tff(c_50, plain, (v4_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.91  tff(c_1351, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1350, c_50])).
% 4.33/1.91  tff(c_1349, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 4.33/1.91  tff(c_1399, plain, (![A_174, B_175]: (k2_pre_topc(A_174, B_175)=B_175 | ~v4_pre_topc(B_175, A_174) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.33/1.91  tff(c_1405, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1399])).
% 4.33/1.91  tff(c_1412, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1349, c_1405])).
% 4.33/1.91  tff(c_1361, plain, (![B_168, A_169]: (r1_tarski(B_168, k2_pre_topc(A_169, B_168)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.33/1.91  tff(c_1363, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1361])).
% 4.33/1.91  tff(c_1368, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1363])).
% 4.33/1.91  tff(c_1385, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1368, c_2])).
% 4.33/1.91  tff(c_1390, plain, (~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1385])).
% 4.33/1.91  tff(c_1416, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_1390])).
% 4.33/1.91  tff(c_1420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1416])).
% 4.33/1.91  tff(c_1421, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1385])).
% 4.33/1.91  tff(c_1512, plain, (![A_192, B_193]: (r1_tarski(k1_tops_1(A_192, k2_pre_topc(A_192, B_193)), B_193) | ~v4_tops_1(B_193, A_192) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.33/1.91  tff(c_1520, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1421, c_1512])).
% 4.33/1.91  tff(c_1525, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1351, c_1520])).
% 4.33/1.91  tff(c_1568, plain, (![A_200, B_201, C_202]: (r1_tarski(k2_pre_topc(A_200, B_201), k2_pre_topc(A_200, C_202)) | ~r1_tarski(B_201, C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(u1_struct_0(A_200))) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.33/1.91  tff(c_1594, plain, (![B_201]: (r1_tarski(k2_pre_topc('#skF_2', B_201), '#skF_4') | ~r1_tarski(B_201, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1421, c_1568])).
% 4.33/1.91  tff(c_1626, plain, (![B_204]: (r1_tarski(k2_pre_topc('#skF_2', B_204), '#skF_4') | ~r1_tarski(B_204, '#skF_4') | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1594])).
% 4.33/1.91  tff(c_1630, plain, (![B_25]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_25)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_25), '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_1626])).
% 4.33/1.91  tff(c_1636, plain, (![B_25]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_25)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_25), '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1630])).
% 4.33/1.91  tff(c_1526, plain, (![B_194, A_195]: (r1_tarski(B_194, k2_pre_topc(A_195, k1_tops_1(A_195, B_194))) | ~v4_tops_1(B_194, A_195) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.33/1.91  tff(c_1705, plain, (![A_213, B_214]: (k2_pre_topc(A_213, k1_tops_1(A_213, B_214))=B_214 | ~r1_tarski(k2_pre_topc(A_213, k1_tops_1(A_213, B_214)), B_214) | ~v4_tops_1(B_214, A_213) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(resolution, [status(thm)], [c_1526, c_2])).
% 4.33/1.91  tff(c_1709, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1636, c_1705])).
% 4.33/1.91  tff(c_1716, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1525, c_36, c_1351, c_1709])).
% 4.33/1.91  tff(c_1752, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1716, c_24])).
% 4.33/1.91  tff(c_1777, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1752])).
% 4.33/1.91  tff(c_1779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_1777])).
% 4.33/1.91  tff(c_1780, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.33/1.91  tff(c_1874, plain, (![A_229, B_230]: (k2_pre_topc(A_229, k1_tops_1(A_229, B_230))=B_230 | ~v5_tops_1(B_230, A_229) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.33/1.91  tff(c_1880, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1874])).
% 4.33/1.91  tff(c_1887, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1780, c_1880])).
% 4.33/1.91  tff(c_1839, plain, (![A_223, B_224]: (m1_subset_1(k1_tops_1(A_223, B_224), k1_zfmisc_1(u1_struct_0(A_223))) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.33/1.91  tff(c_1925, plain, (![A_233, B_234]: (v4_pre_topc(k2_pre_topc(A_233, k1_tops_1(A_233, B_234)), A_233) | ~v2_pre_topc(A_233) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_1839, c_30])).
% 4.33/1.91  tff(c_1928, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1887, c_1925])).
% 4.33/1.91  tff(c_1933, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_40, c_1928])).
% 4.33/1.91  tff(c_1935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1791, c_1933])).
% 4.33/1.91  tff(c_1937, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.33/1.91  tff(c_1781, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.33/1.91  tff(c_42, plain, (~v5_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.33/1.91  tff(c_1939, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_1781, c_42])).
% 4.33/1.91  tff(c_2231, plain, (![A_271, B_272]: (k2_pre_topc(A_271, k1_tops_1(A_271, B_272))=B_272 | ~v5_tops_1(B_272, A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.33/1.91  tff(c_2237, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_2231])).
% 4.33/1.91  tff(c_2244, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1780, c_2237])).
% 4.33/1.91  tff(c_2168, plain, (![A_261, B_262]: (m1_subset_1(k1_tops_1(A_261, B_262), k1_zfmisc_1(u1_struct_0(A_261))) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.33/1.91  tff(c_2289, plain, (![A_277, B_278]: (r1_tarski(k1_tops_1(A_277, B_278), k2_pre_topc(A_277, k1_tops_1(A_277, B_278))) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_277))) | ~l1_pre_topc(A_277))), inference(resolution, [status(thm)], [c_2168, c_10])).
% 4.33/1.91  tff(c_2294, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2244, c_2289])).
% 4.33/1.91  tff(c_2300, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_2294])).
% 4.33/1.91  tff(c_1959, plain, (![A_237, B_238]: (k2_pre_topc(A_237, B_238)=B_238 | ~v4_pre_topc(B_238, A_237) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0(A_237))) | ~l1_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.33/1.91  tff(c_1965, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1959])).
% 4.33/1.91  tff(c_1971, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1937, c_1965])).
% 4.33/1.91  tff(c_2468, plain, (![B_294, A_295]: (v4_tops_1(B_294, A_295) | ~r1_tarski(B_294, k2_pre_topc(A_295, k1_tops_1(A_295, B_294))) | ~r1_tarski(k1_tops_1(A_295, k2_pre_topc(A_295, B_294)), B_294) | ~m1_subset_1(B_294, k1_zfmisc_1(u1_struct_0(A_295))) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.33/1.91  tff(c_2483, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1971, c_2468])).
% 4.33/1.91  tff(c_2492, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_2300, c_6, c_2244, c_2483])).
% 4.33/1.91  tff(c_2494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1939, c_2492])).
% 4.33/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.91  
% 4.33/1.91  Inference rules
% 4.33/1.91  ----------------------
% 4.33/1.91  #Ref     : 0
% 4.33/1.91  #Sup     : 479
% 4.33/1.91  #Fact    : 0
% 4.33/1.91  #Define  : 0
% 4.33/1.91  #Split   : 56
% 4.33/1.91  #Chain   : 0
% 4.33/1.91  #Close   : 0
% 4.33/1.91  
% 4.33/1.91  Ordering : KBO
% 4.33/1.91  
% 4.33/1.91  Simplification rules
% 4.33/1.91  ----------------------
% 4.33/1.91  #Subsume      : 51
% 4.33/1.91  #Demod        : 722
% 4.33/1.91  #Tautology    : 179
% 4.33/1.91  #SimpNegUnit  : 21
% 4.33/1.91  #BackRed      : 24
% 4.33/1.91  
% 4.33/1.91  #Partial instantiations: 0
% 4.33/1.91  #Strategies tried      : 1
% 4.33/1.91  
% 4.33/1.91  Timing (in seconds)
% 4.33/1.91  ----------------------
% 4.66/1.91  Preprocessing        : 0.34
% 4.66/1.91  Parsing              : 0.19
% 4.66/1.91  CNF conversion       : 0.02
% 4.66/1.91  Main loop            : 0.66
% 4.66/1.91  Inferencing          : 0.23
% 4.66/1.91  Reduction            : 0.22
% 4.66/1.91  Demodulation         : 0.15
% 4.66/1.91  BG Simplification    : 0.03
% 4.66/1.91  Subsumption          : 0.13
% 4.66/1.91  Abstraction          : 0.03
% 4.66/1.91  MUC search           : 0.00
% 4.66/1.91  Cooper               : 0.00
% 4.66/1.91  Total                : 1.07
% 4.66/1.91  Index Insertion      : 0.00
% 4.66/1.91  Index Deletion       : 0.00
% 4.66/1.91  Index Matching       : 0.00
% 4.66/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
