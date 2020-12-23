%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:46 EST 2020

% Result     : Theorem 15.01s
% Output     : CNFRefutation 15.12s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 357 expanded)
%              Number of leaves         :   37 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  351 (1126 expanded)
%              Number of equality atoms :   34 (  60 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44445,plain,(
    ! [A_1045,B_1046] :
      ( v3_pre_topc(k1_tops_1(A_1045,B_1046),A_1045)
      | ~ m1_subset_1(B_1046,k1_zfmisc_1(u1_struct_0(A_1045)))
      | ~ l1_pre_topc(A_1045)
      | ~ v2_pre_topc(A_1045) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44452,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_44445])).

tff(c_44457,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_44452])).

tff(c_44140,plain,(
    ! [A_1033,B_1034] :
      ( r1_tarski(k1_tops_1(A_1033,B_1034),B_1034)
      | ~ m1_subset_1(B_1034,k1_zfmisc_1(u1_struct_0(A_1033)))
      | ~ l1_pre_topc(A_1033) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44145,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_44140])).

tff(c_44149,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44145])).

tff(c_41633,plain,(
    ! [A_909,B_910] :
      ( v3_pre_topc(k1_tops_1(A_909,B_910),A_909)
      | ~ m1_subset_1(B_910,k1_zfmisc_1(u1_struct_0(A_909)))
      | ~ l1_pre_topc(A_909)
      | ~ v2_pre_topc(A_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_41638,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_41633])).

tff(c_41642,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_41638])).

tff(c_41327,plain,(
    ! [A_894,B_895] :
      ( r1_tarski(k1_tops_1(A_894,B_895),B_895)
      | ~ m1_subset_1(B_895,k1_zfmisc_1(u1_struct_0(A_894)))
      | ~ l1_pre_topc(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_41332,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_41327])).

tff(c_41336,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_41332])).

tff(c_40663,plain,(
    ! [A_843,B_844] :
      ( v3_pre_topc(k1_tops_1(A_843,B_844),A_843)
      | ~ m1_subset_1(B_844,k1_zfmisc_1(u1_struct_0(A_843)))
      | ~ l1_pre_topc(A_843)
      | ~ v2_pre_topc(A_843) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40670,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_40663])).

tff(c_40675,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40670])).

tff(c_40254,plain,(
    ! [A_824,B_825] :
      ( r1_tarski(k1_tops_1(A_824,B_825),B_825)
      | ~ m1_subset_1(B_825,k1_zfmisc_1(u1_struct_0(A_824)))
      | ~ l1_pre_topc(A_824) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40259,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_40254])).

tff(c_40263,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40259])).

tff(c_39319,plain,(
    ! [A_767,B_768] :
      ( v3_pre_topc(k1_tops_1(A_767,B_768),A_767)
      | ~ m1_subset_1(B_768,k1_zfmisc_1(u1_struct_0(A_767)))
      | ~ l1_pre_topc(A_767)
      | ~ v2_pre_topc(A_767) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_39324,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_39319])).

tff(c_39328,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_39324])).

tff(c_39205,plain,(
    ! [A_761,B_762] :
      ( r1_tarski(k1_tops_1(A_761,B_762),B_762)
      | ~ m1_subset_1(B_762,k1_zfmisc_1(u1_struct_0(A_761)))
      | ~ l1_pre_topc(A_761) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_39210,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_39205])).

tff(c_39214,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_39210])).

tff(c_62,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_133,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_150,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_92,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_66,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_158,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_295,plain,(
    ! [A_80,B_81] :
      ( k3_subset_1(A_80,k3_subset_1(A_80,B_81)) = B_81
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_303,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_158,c_295])).

tff(c_36,plain,(
    ! [A_29,B_31] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_29),B_31),A_29)
      | ~ v3_pre_topc(B_31,A_29)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k3_subset_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_649,plain,(
    ! [A_97,B_98] :
      ( k2_pre_topc(A_97,B_98) = B_98
      | ~ v4_pre_topc(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7004,plain,(
    ! [A_259,B_260] :
      ( k2_pre_topc(A_259,k3_subset_1(u1_struct_0(A_259),B_260)) = k3_subset_1(u1_struct_0(A_259),B_260)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_259),B_260),A_259)
      | ~ l1_pre_topc(A_259)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259))) ) ),
    inference(resolution,[status(thm)],[c_20,c_649])).

tff(c_29285,plain,(
    ! [A_522,B_523] :
      ( k2_pre_topc(A_522,k3_subset_1(u1_struct_0(A_522),B_523)) = k3_subset_1(u1_struct_0(A_522),B_523)
      | ~ v3_pre_topc(B_523,A_522)
      | ~ m1_subset_1(B_523,k1_zfmisc_1(u1_struct_0(A_522)))
      | ~ l1_pre_topc(A_522) ) ),
    inference(resolution,[status(thm)],[c_36,c_7004])).

tff(c_29296,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_158,c_29285])).

tff(c_29311,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_133,c_29296])).

tff(c_28,plain,(
    ! [A_22,B_24] :
      ( k3_subset_1(u1_struct_0(A_22),k2_pre_topc(A_22,k3_subset_1(u1_struct_0(A_22),B_24))) = k1_tops_1(A_22,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_29327,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_29311,c_28])).

tff(c_29338,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_158,c_303,c_29327])).

tff(c_367,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(k1_tops_1(A_87,B_88),B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_372,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_158,c_367])).

tff(c_378,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_372])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_394,plain,
    ( k1_tops_1('#skF_1','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_378,c_2])).

tff(c_1157,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_29397,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29338,c_1157])).

tff(c_29431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_29397])).

tff(c_29432,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_29988,plain,(
    ! [A_551,B_552,C_553] :
      ( r1_tarski(k1_tops_1(A_551,B_552),k1_tops_1(A_551,C_553))
      | ~ r1_tarski(B_552,C_553)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(u1_struct_0(A_551)))
      | ~ m1_subset_1(B_552,k1_zfmisc_1(u1_struct_0(A_551)))
      | ~ l1_pre_topc(A_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38035,plain,(
    ! [A_723,B_724,C_725] :
      ( k2_xboole_0(k1_tops_1(A_723,B_724),k1_tops_1(A_723,C_725)) = k1_tops_1(A_723,C_725)
      | ~ r1_tarski(B_724,C_725)
      | ~ m1_subset_1(C_725,k1_zfmisc_1(u1_struct_0(A_723)))
      | ~ m1_subset_1(B_724,k1_zfmisc_1(u1_struct_0(A_723)))
      | ~ l1_pre_topc(A_723) ) ),
    inference(resolution,[status(thm)],[c_29988,c_10])).

tff(c_38046,plain,(
    ! [B_724] :
      ( k2_xboole_0(k1_tops_1('#skF_1',B_724),k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
      | ~ r1_tarski(B_724,'#skF_3')
      | ~ m1_subset_1(B_724,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_38035])).

tff(c_38239,plain,(
    ! [B_729] :
      ( k2_xboole_0(k1_tops_1('#skF_1',B_729),k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
      | ~ r1_tarski(B_729,'#skF_3')
      | ~ m1_subset_1(B_729,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38046])).

tff(c_38253,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_4'),k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_38239])).

tff(c_38264,plain,(
    k2_xboole_0('#skF_4',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_29432,c_38253])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_335,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(k2_xboole_0(A_84,C_85),B_86)
      | ~ r1_tarski(C_85,B_86)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(k2_xboole_0(A_8,B_9),A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_120])).

tff(c_343,plain,(
    ! [B_86,C_85] :
      ( k2_xboole_0(B_86,C_85) = B_86
      | ~ r1_tarski(C_85,B_86)
      | ~ r1_tarski(B_86,B_86) ) ),
    inference(resolution,[status(thm)],[c_335,c_128])).

tff(c_447,plain,(
    ! [B_89,C_90] :
      ( k2_xboole_0(B_89,C_90) = B_89
      | ~ r1_tarski(C_90,B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_343])).

tff(c_478,plain,(
    ! [A_8,B_9] : k2_xboole_0(k2_xboole_0(A_8,B_9),A_8) = k2_xboole_0(A_8,B_9) ),
    inference(resolution,[status(thm)],[c_12,c_447])).

tff(c_38362,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_4') = k2_xboole_0('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38264,c_478])).

tff(c_38401,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_4') = k1_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38264,c_38362])).

tff(c_111,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_118,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(k1_tarski(A_62),B_63) = B_63
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_111,c_10])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29850,plain,(
    ! [C_548,B_549,A_550] :
      ( k2_xboole_0(k2_xboole_0(C_548,B_549),A_550) = k2_xboole_0(C_548,B_549)
      | ~ r1_tarski(A_550,B_549) ) ),
    inference(resolution,[status(thm)],[c_8,c_447])).

tff(c_30061,plain,(
    ! [A_556,C_557,B_558,A_559] :
      ( r1_tarski(A_556,k2_xboole_0(C_557,B_558))
      | ~ r1_tarski(A_556,A_559)
      | ~ r1_tarski(A_559,B_558) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29850,c_8])).

tff(c_31423,plain,(
    ! [A_588,C_589,B_590,B_591] :
      ( r1_tarski(A_588,k2_xboole_0(C_589,B_590))
      | ~ r1_tarski(k2_xboole_0(A_588,B_591),B_590) ) ),
    inference(resolution,[status(thm)],[c_12,c_30061])).

tff(c_31487,plain,(
    ! [A_592,C_593,B_594] : r1_tarski(A_592,k2_xboole_0(C_593,k2_xboole_0(A_592,B_594))) ),
    inference(resolution,[status(thm)],[c_6,c_31423])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32688,plain,(
    ! [A_616,C_617,B_618] : r2_hidden(A_616,k2_xboole_0(C_617,k2_xboole_0(k1_tarski(A_616),B_618))) ),
    inference(resolution,[status(thm)],[c_31487,c_16])).

tff(c_32726,plain,(
    ! [A_62,C_617,B_63] :
      ( r2_hidden(A_62,k2_xboole_0(C_617,B_63))
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_32688])).

tff(c_38865,plain,(
    ! [A_737] :
      ( r2_hidden(A_737,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_737,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38401,c_32726])).

tff(c_48,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_2',D_50)
      | ~ r1_tarski(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_1')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_980,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_38880,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_38865,c_980])).

tff(c_38888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38880])).

tff(c_38908,plain,(
    ! [D_739] :
      ( ~ r2_hidden('#skF_2',D_739)
      | ~ r1_tarski(D_739,'#skF_3')
      | ~ v3_pre_topc(D_739,'#skF_1')
      | ~ m1_subset_1(D_739,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_38919,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_158,c_38908])).

tff(c_38930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_150,c_92,c_38919])).

tff(c_38931,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_39697,plain,(
    ! [A_784,B_785] :
      ( m1_subset_1(k1_tops_1(A_784,B_785),k1_zfmisc_1(u1_struct_0(A_784)))
      | ~ m1_subset_1(B_785,k1_zfmisc_1(u1_struct_0(A_784)))
      | ~ l1_pre_topc(A_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_39472,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_2',D_50)
      | ~ r1_tarski(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_1')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38931,c_48])).

tff(c_39704,plain,(
    ! [B_785] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_785))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_785),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_785),'#skF_1')
      | ~ m1_subset_1(B_785,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_39697,c_39472])).

tff(c_39980,plain,(
    ! [B_801] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_801))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_801),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_801),'#skF_1')
      | ~ m1_subset_1(B_801,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_39704])).

tff(c_39991,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_39980])).

tff(c_39999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39328,c_39214,c_38931,c_39991])).

tff(c_40000,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_40476,plain,(
    ! [A_833,B_834] :
      ( m1_subset_1(k1_tops_1(A_833,B_834),k1_zfmisc_1(u1_struct_0(A_833)))
      | ~ m1_subset_1(B_834,k1_zfmisc_1(u1_struct_0(A_833)))
      | ~ l1_pre_topc(A_833) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40001,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_2',D_50)
      | ~ r1_tarski(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_1')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_40326,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_2',D_50)
      | ~ r1_tarski(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_1')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40001,c_56])).

tff(c_40480,plain,(
    ! [B_834] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_834))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_834),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_834),'#skF_1')
      | ~ m1_subset_1(B_834,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40476,c_40326])).

tff(c_41095,plain,(
    ! [B_870] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_870))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_870),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_870),'#skF_1')
      | ~ m1_subset_1(B_870,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40480])).

tff(c_41106,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_41095])).

tff(c_41114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40675,c_40263,c_40000,c_41106])).

tff(c_41115,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_41786,plain,(
    ! [A_915,B_916] :
      ( m1_subset_1(k1_tops_1(A_915,B_916),k1_zfmisc_1(u1_struct_0(A_915)))
      | ~ m1_subset_1(B_916,k1_zfmisc_1(u1_struct_0(A_915)))
      | ~ l1_pre_topc(A_915) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_41116,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_2',D_50)
      | ~ r1_tarski(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_1')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_41399,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_2',D_50)
      | ~ r1_tarski(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_1')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_41116,c_60])).

tff(c_41795,plain,(
    ! [B_916] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_916))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_916),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_916),'#skF_1')
      | ~ m1_subset_1(B_916,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_41786,c_41399])).

tff(c_43687,plain,(
    ! [B_994] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_994))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_994),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_994),'#skF_1')
      | ~ m1_subset_1(B_994,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_41795])).

tff(c_43698,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_43687])).

tff(c_43706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41642,c_41336,c_41115,c_43698])).

tff(c_43707,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_44289,plain,(
    ! [A_1041,B_1042] :
      ( m1_subset_1(k1_tops_1(A_1041,B_1042),k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ m1_subset_1(B_1042,k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ l1_pre_topc(A_1041) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_43708,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_2',D_50)
      | ~ r1_tarski(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_1')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44232,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_2',D_50)
      | ~ r1_tarski(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_1')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_43708,c_52])).

tff(c_44296,plain,(
    ! [B_1042] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_1042))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_1042),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_1042),'#skF_1')
      | ~ m1_subset_1(B_1042,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44289,c_44232])).

tff(c_44860,plain,(
    ! [B_1069] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_1069))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_1069),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_1069),'#skF_1')
      | ~ m1_subset_1(B_1069,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44296])).

tff(c_44871,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_44860])).

tff(c_44879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44457,c_44149,c_43707,c_44871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:37:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.01/6.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.01/6.76  
% 15.01/6.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.01/6.76  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.01/6.76  
% 15.01/6.76  %Foreground sorts:
% 15.01/6.76  
% 15.01/6.76  
% 15.01/6.76  %Background operators:
% 15.01/6.76  
% 15.01/6.76  
% 15.01/6.76  %Foreground operators:
% 15.01/6.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 15.01/6.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.01/6.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.01/6.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.01/6.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.01/6.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.01/6.76  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.01/6.76  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 15.01/6.76  tff('#skF_2', type, '#skF_2': $i).
% 15.01/6.76  tff('#skF_3', type, '#skF_3': $i).
% 15.01/6.76  tff('#skF_1', type, '#skF_1': $i).
% 15.01/6.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.01/6.76  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 15.01/6.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.01/6.76  tff('#skF_4', type, '#skF_4': $i).
% 15.01/6.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.01/6.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.01/6.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.01/6.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.01/6.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 15.01/6.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.01/6.76  
% 15.12/6.79  tff(f_142, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 15.12/6.79  tff(f_95, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 15.12/6.79  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 15.12/6.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.12/6.79  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 15.12/6.79  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 15.12/6.79  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 15.12/6.79  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 15.12/6.79  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 15.12/6.79  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 15.12/6.79  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 15.12/6.79  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 15.12/6.79  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 15.12/6.79  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 15.12/6.79  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 15.12/6.79  tff(f_87, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 15.12/6.79  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_44445, plain, (![A_1045, B_1046]: (v3_pre_topc(k1_tops_1(A_1045, B_1046), A_1045) | ~m1_subset_1(B_1046, k1_zfmisc_1(u1_struct_0(A_1045))) | ~l1_pre_topc(A_1045) | ~v2_pre_topc(A_1045))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.12/6.79  tff(c_44452, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_44445])).
% 15.12/6.79  tff(c_44457, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_44452])).
% 15.12/6.79  tff(c_44140, plain, (![A_1033, B_1034]: (r1_tarski(k1_tops_1(A_1033, B_1034), B_1034) | ~m1_subset_1(B_1034, k1_zfmisc_1(u1_struct_0(A_1033))) | ~l1_pre_topc(A_1033))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.12/6.79  tff(c_44145, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_44140])).
% 15.12/6.79  tff(c_44149, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44145])).
% 15.12/6.79  tff(c_41633, plain, (![A_909, B_910]: (v3_pre_topc(k1_tops_1(A_909, B_910), A_909) | ~m1_subset_1(B_910, k1_zfmisc_1(u1_struct_0(A_909))) | ~l1_pre_topc(A_909) | ~v2_pre_topc(A_909))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.12/6.79  tff(c_41638, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_41633])).
% 15.12/6.79  tff(c_41642, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_41638])).
% 15.12/6.79  tff(c_41327, plain, (![A_894, B_895]: (r1_tarski(k1_tops_1(A_894, B_895), B_895) | ~m1_subset_1(B_895, k1_zfmisc_1(u1_struct_0(A_894))) | ~l1_pre_topc(A_894))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.12/6.79  tff(c_41332, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_41327])).
% 15.12/6.79  tff(c_41336, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_41332])).
% 15.12/6.79  tff(c_40663, plain, (![A_843, B_844]: (v3_pre_topc(k1_tops_1(A_843, B_844), A_843) | ~m1_subset_1(B_844, k1_zfmisc_1(u1_struct_0(A_843))) | ~l1_pre_topc(A_843) | ~v2_pre_topc(A_843))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.12/6.79  tff(c_40670, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_40663])).
% 15.12/6.79  tff(c_40675, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40670])).
% 15.12/6.79  tff(c_40254, plain, (![A_824, B_825]: (r1_tarski(k1_tops_1(A_824, B_825), B_825) | ~m1_subset_1(B_825, k1_zfmisc_1(u1_struct_0(A_824))) | ~l1_pre_topc(A_824))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.12/6.79  tff(c_40259, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_40254])).
% 15.12/6.79  tff(c_40263, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40259])).
% 15.12/6.79  tff(c_39319, plain, (![A_767, B_768]: (v3_pre_topc(k1_tops_1(A_767, B_768), A_767) | ~m1_subset_1(B_768, k1_zfmisc_1(u1_struct_0(A_767))) | ~l1_pre_topc(A_767) | ~v2_pre_topc(A_767))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.12/6.79  tff(c_39324, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_39319])).
% 15.12/6.79  tff(c_39328, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_39324])).
% 15.12/6.79  tff(c_39205, plain, (![A_761, B_762]: (r1_tarski(k1_tops_1(A_761, B_762), B_762) | ~m1_subset_1(B_762, k1_zfmisc_1(u1_struct_0(A_761))) | ~l1_pre_topc(A_761))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.12/6.79  tff(c_39210, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_39205])).
% 15.12/6.79  tff(c_39214, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_39210])).
% 15.12/6.79  tff(c_62, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_133, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_62])).
% 15.12/6.79  tff(c_58, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_150, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 15.12/6.79  tff(c_54, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_92, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 15.12/6.79  tff(c_66, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_158, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_66])).
% 15.12/6.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.12/6.79  tff(c_295, plain, (![A_80, B_81]: (k3_subset_1(A_80, k3_subset_1(A_80, B_81))=B_81 | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.12/6.79  tff(c_303, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_158, c_295])).
% 15.12/6.79  tff(c_36, plain, (![A_29, B_31]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_29), B_31), A_29) | ~v3_pre_topc(B_31, A_29) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.12/6.79  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(k3_subset_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.12/6.79  tff(c_649, plain, (![A_97, B_98]: (k2_pre_topc(A_97, B_98)=B_98 | ~v4_pre_topc(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.12/6.79  tff(c_7004, plain, (![A_259, B_260]: (k2_pre_topc(A_259, k3_subset_1(u1_struct_0(A_259), B_260))=k3_subset_1(u1_struct_0(A_259), B_260) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_259), B_260), A_259) | ~l1_pre_topc(A_259) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))))), inference(resolution, [status(thm)], [c_20, c_649])).
% 15.12/6.79  tff(c_29285, plain, (![A_522, B_523]: (k2_pre_topc(A_522, k3_subset_1(u1_struct_0(A_522), B_523))=k3_subset_1(u1_struct_0(A_522), B_523) | ~v3_pre_topc(B_523, A_522) | ~m1_subset_1(B_523, k1_zfmisc_1(u1_struct_0(A_522))) | ~l1_pre_topc(A_522))), inference(resolution, [status(thm)], [c_36, c_7004])).
% 15.12/6.79  tff(c_29296, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_158, c_29285])).
% 15.12/6.79  tff(c_29311, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_133, c_29296])).
% 15.12/6.79  tff(c_28, plain, (![A_22, B_24]: (k3_subset_1(u1_struct_0(A_22), k2_pre_topc(A_22, k3_subset_1(u1_struct_0(A_22), B_24)))=k1_tops_1(A_22, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.12/6.79  tff(c_29327, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_29311, c_28])).
% 15.12/6.79  tff(c_29338, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_158, c_303, c_29327])).
% 15.12/6.79  tff(c_367, plain, (![A_87, B_88]: (r1_tarski(k1_tops_1(A_87, B_88), B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.12/6.79  tff(c_372, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_158, c_367])).
% 15.12/6.79  tff(c_378, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_372])).
% 15.12/6.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.12/6.79  tff(c_394, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_378, c_2])).
% 15.12/6.79  tff(c_1157, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_394])).
% 15.12/6.79  tff(c_29397, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29338, c_1157])).
% 15.12/6.79  tff(c_29431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_29397])).
% 15.12/6.79  tff(c_29432, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_394])).
% 15.12/6.79  tff(c_29988, plain, (![A_551, B_552, C_553]: (r1_tarski(k1_tops_1(A_551, B_552), k1_tops_1(A_551, C_553)) | ~r1_tarski(B_552, C_553) | ~m1_subset_1(C_553, k1_zfmisc_1(u1_struct_0(A_551))) | ~m1_subset_1(B_552, k1_zfmisc_1(u1_struct_0(A_551))) | ~l1_pre_topc(A_551))), inference(cnfTransformation, [status(thm)], [f_123])).
% 15.12/6.79  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.12/6.79  tff(c_38035, plain, (![A_723, B_724, C_725]: (k2_xboole_0(k1_tops_1(A_723, B_724), k1_tops_1(A_723, C_725))=k1_tops_1(A_723, C_725) | ~r1_tarski(B_724, C_725) | ~m1_subset_1(C_725, k1_zfmisc_1(u1_struct_0(A_723))) | ~m1_subset_1(B_724, k1_zfmisc_1(u1_struct_0(A_723))) | ~l1_pre_topc(A_723))), inference(resolution, [status(thm)], [c_29988, c_10])).
% 15.12/6.79  tff(c_38046, plain, (![B_724]: (k2_xboole_0(k1_tops_1('#skF_1', B_724), k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski(B_724, '#skF_3') | ~m1_subset_1(B_724, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_38035])).
% 15.12/6.79  tff(c_38239, plain, (![B_729]: (k2_xboole_0(k1_tops_1('#skF_1', B_729), k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski(B_729, '#skF_3') | ~m1_subset_1(B_729, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38046])).
% 15.12/6.79  tff(c_38253, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_4'), k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_158, c_38239])).
% 15.12/6.79  tff(c_38264, plain, (k2_xboole_0('#skF_4', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_29432, c_38253])).
% 15.12/6.79  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.12/6.79  tff(c_335, plain, (![A_84, C_85, B_86]: (r1_tarski(k2_xboole_0(A_84, C_85), B_86) | ~r1_tarski(C_85, B_86) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.12/6.79  tff(c_120, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.12/6.79  tff(c_128, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(k2_xboole_0(A_8, B_9), A_8))), inference(resolution, [status(thm)], [c_12, c_120])).
% 15.12/6.79  tff(c_343, plain, (![B_86, C_85]: (k2_xboole_0(B_86, C_85)=B_86 | ~r1_tarski(C_85, B_86) | ~r1_tarski(B_86, B_86))), inference(resolution, [status(thm)], [c_335, c_128])).
% 15.12/6.79  tff(c_447, plain, (![B_89, C_90]: (k2_xboole_0(B_89, C_90)=B_89 | ~r1_tarski(C_90, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_343])).
% 15.12/6.79  tff(c_478, plain, (![A_8, B_9]: (k2_xboole_0(k2_xboole_0(A_8, B_9), A_8)=k2_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_447])).
% 15.12/6.79  tff(c_38362, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_4')=k2_xboole_0('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38264, c_478])).
% 15.12/6.79  tff(c_38401, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_4')=k1_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38264, c_38362])).
% 15.12/6.79  tff(c_111, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.12/6.79  tff(c_118, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), B_63)=B_63 | ~r2_hidden(A_62, B_63))), inference(resolution, [status(thm)], [c_111, c_10])).
% 15.12/6.79  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.12/6.79  tff(c_29850, plain, (![C_548, B_549, A_550]: (k2_xboole_0(k2_xboole_0(C_548, B_549), A_550)=k2_xboole_0(C_548, B_549) | ~r1_tarski(A_550, B_549))), inference(resolution, [status(thm)], [c_8, c_447])).
% 15.12/6.79  tff(c_30061, plain, (![A_556, C_557, B_558, A_559]: (r1_tarski(A_556, k2_xboole_0(C_557, B_558)) | ~r1_tarski(A_556, A_559) | ~r1_tarski(A_559, B_558))), inference(superposition, [status(thm), theory('equality')], [c_29850, c_8])).
% 15.12/6.79  tff(c_31423, plain, (![A_588, C_589, B_590, B_591]: (r1_tarski(A_588, k2_xboole_0(C_589, B_590)) | ~r1_tarski(k2_xboole_0(A_588, B_591), B_590))), inference(resolution, [status(thm)], [c_12, c_30061])).
% 15.12/6.79  tff(c_31487, plain, (![A_592, C_593, B_594]: (r1_tarski(A_592, k2_xboole_0(C_593, k2_xboole_0(A_592, B_594))))), inference(resolution, [status(thm)], [c_6, c_31423])).
% 15.12/6.79  tff(c_16, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.12/6.79  tff(c_32688, plain, (![A_616, C_617, B_618]: (r2_hidden(A_616, k2_xboole_0(C_617, k2_xboole_0(k1_tarski(A_616), B_618))))), inference(resolution, [status(thm)], [c_31487, c_16])).
% 15.12/6.79  tff(c_32726, plain, (![A_62, C_617, B_63]: (r2_hidden(A_62, k2_xboole_0(C_617, B_63)) | ~r2_hidden(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_118, c_32688])).
% 15.12/6.79  tff(c_38865, plain, (![A_737]: (r2_hidden(A_737, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_737, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_38401, c_32726])).
% 15.12/6.79  tff(c_48, plain, (![D_50]: (~r2_hidden('#skF_2', D_50) | ~r1_tarski(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_1') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_980, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 15.12/6.79  tff(c_38880, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_38865, c_980])).
% 15.12/6.79  tff(c_38888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_38880])).
% 15.12/6.79  tff(c_38908, plain, (![D_739]: (~r2_hidden('#skF_2', D_739) | ~r1_tarski(D_739, '#skF_3') | ~v3_pre_topc(D_739, '#skF_1') | ~m1_subset_1(D_739, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_48])).
% 15.12/6.79  tff(c_38919, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_158, c_38908])).
% 15.12/6.79  tff(c_38930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_150, c_92, c_38919])).
% 15.12/6.79  tff(c_38931, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 15.12/6.79  tff(c_39697, plain, (![A_784, B_785]: (m1_subset_1(k1_tops_1(A_784, B_785), k1_zfmisc_1(u1_struct_0(A_784))) | ~m1_subset_1(B_785, k1_zfmisc_1(u1_struct_0(A_784))) | ~l1_pre_topc(A_784))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.12/6.79  tff(c_39472, plain, (![D_50]: (~r2_hidden('#skF_2', D_50) | ~r1_tarski(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_1') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38931, c_48])).
% 15.12/6.79  tff(c_39704, plain, (![B_785]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_785)) | ~r1_tarski(k1_tops_1('#skF_1', B_785), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_785), '#skF_1') | ~m1_subset_1(B_785, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_39697, c_39472])).
% 15.12/6.79  tff(c_39980, plain, (![B_801]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_801)) | ~r1_tarski(k1_tops_1('#skF_1', B_801), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_801), '#skF_1') | ~m1_subset_1(B_801, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_39704])).
% 15.12/6.79  tff(c_39991, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_42, c_39980])).
% 15.12/6.79  tff(c_39999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39328, c_39214, c_38931, c_39991])).
% 15.12/6.79  tff(c_40000, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 15.12/6.79  tff(c_40476, plain, (![A_833, B_834]: (m1_subset_1(k1_tops_1(A_833, B_834), k1_zfmisc_1(u1_struct_0(A_833))) | ~m1_subset_1(B_834, k1_zfmisc_1(u1_struct_0(A_833))) | ~l1_pre_topc(A_833))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.12/6.79  tff(c_40001, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 15.12/6.79  tff(c_56, plain, (![D_50]: (~r2_hidden('#skF_2', D_50) | ~r1_tarski(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_1') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_40326, plain, (![D_50]: (~r2_hidden('#skF_2', D_50) | ~r1_tarski(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_1') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40001, c_56])).
% 15.12/6.79  tff(c_40480, plain, (![B_834]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_834)) | ~r1_tarski(k1_tops_1('#skF_1', B_834), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_834), '#skF_1') | ~m1_subset_1(B_834, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40476, c_40326])).
% 15.12/6.79  tff(c_41095, plain, (![B_870]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_870)) | ~r1_tarski(k1_tops_1('#skF_1', B_870), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_870), '#skF_1') | ~m1_subset_1(B_870, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40480])).
% 15.12/6.79  tff(c_41106, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_42, c_41095])).
% 15.12/6.79  tff(c_41114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40675, c_40263, c_40000, c_41106])).
% 15.12/6.79  tff(c_41115, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 15.12/6.79  tff(c_41786, plain, (![A_915, B_916]: (m1_subset_1(k1_tops_1(A_915, B_916), k1_zfmisc_1(u1_struct_0(A_915))) | ~m1_subset_1(B_916, k1_zfmisc_1(u1_struct_0(A_915))) | ~l1_pre_topc(A_915))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.12/6.79  tff(c_41116, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 15.12/6.79  tff(c_60, plain, (![D_50]: (~r2_hidden('#skF_2', D_50) | ~r1_tarski(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_1') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_41399, plain, (![D_50]: (~r2_hidden('#skF_2', D_50) | ~r1_tarski(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_1') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_41116, c_60])).
% 15.12/6.79  tff(c_41795, plain, (![B_916]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_916)) | ~r1_tarski(k1_tops_1('#skF_1', B_916), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_916), '#skF_1') | ~m1_subset_1(B_916, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_41786, c_41399])).
% 15.12/6.79  tff(c_43687, plain, (![B_994]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_994)) | ~r1_tarski(k1_tops_1('#skF_1', B_994), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_994), '#skF_1') | ~m1_subset_1(B_994, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_41795])).
% 15.12/6.79  tff(c_43698, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_42, c_43687])).
% 15.12/6.79  tff(c_43706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41642, c_41336, c_41115, c_43698])).
% 15.12/6.79  tff(c_43707, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 15.12/6.79  tff(c_44289, plain, (![A_1041, B_1042]: (m1_subset_1(k1_tops_1(A_1041, B_1042), k1_zfmisc_1(u1_struct_0(A_1041))) | ~m1_subset_1(B_1042, k1_zfmisc_1(u1_struct_0(A_1041))) | ~l1_pre_topc(A_1041))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.12/6.79  tff(c_43708, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 15.12/6.79  tff(c_52, plain, (![D_50]: (~r2_hidden('#skF_2', D_50) | ~r1_tarski(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_1') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.12/6.79  tff(c_44232, plain, (![D_50]: (~r2_hidden('#skF_2', D_50) | ~r1_tarski(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_1') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_43708, c_52])).
% 15.12/6.79  tff(c_44296, plain, (![B_1042]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_1042)) | ~r1_tarski(k1_tops_1('#skF_1', B_1042), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_1042), '#skF_1') | ~m1_subset_1(B_1042, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44289, c_44232])).
% 15.12/6.79  tff(c_44860, plain, (![B_1069]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_1069)) | ~r1_tarski(k1_tops_1('#skF_1', B_1069), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_1069), '#skF_1') | ~m1_subset_1(B_1069, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44296])).
% 15.12/6.79  tff(c_44871, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_42, c_44860])).
% 15.12/6.79  tff(c_44879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44457, c_44149, c_43707, c_44871])).
% 15.12/6.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.12/6.79  
% 15.12/6.79  Inference rules
% 15.12/6.79  ----------------------
% 15.12/6.79  #Ref     : 0
% 15.12/6.79  #Sup     : 11122
% 15.12/6.79  #Fact    : 0
% 15.12/6.79  #Define  : 0
% 15.12/6.79  #Split   : 40
% 15.12/6.79  #Chain   : 0
% 15.12/6.79  #Close   : 0
% 15.12/6.79  
% 15.12/6.79  Ordering : KBO
% 15.12/6.79  
% 15.12/6.79  Simplification rules
% 15.12/6.79  ----------------------
% 15.12/6.79  #Subsume      : 2600
% 15.12/6.79  #Demod        : 6980
% 15.12/6.79  #Tautology    : 4564
% 15.12/6.79  #SimpNegUnit  : 30
% 15.12/6.79  #BackRed      : 71
% 15.12/6.79  
% 15.12/6.79  #Partial instantiations: 0
% 15.12/6.79  #Strategies tried      : 1
% 15.12/6.79  
% 15.12/6.79  Timing (in seconds)
% 15.12/6.79  ----------------------
% 15.12/6.79  Preprocessing        : 0.33
% 15.12/6.79  Parsing              : 0.18
% 15.12/6.79  CNF conversion       : 0.02
% 15.12/6.79  Main loop            : 5.69
% 15.12/6.79  Inferencing          : 1.08
% 15.12/6.79  Reduction            : 2.48
% 15.12/6.79  Demodulation         : 2.04
% 15.12/6.79  BG Simplification    : 0.12
% 15.12/6.79  Subsumption          : 1.68
% 15.12/6.79  Abstraction          : 0.19
% 15.12/6.79  MUC search           : 0.00
% 15.12/6.79  Cooper               : 0.00
% 15.12/6.79  Total                : 6.07
% 15.12/6.79  Index Insertion      : 0.00
% 15.12/6.79  Index Deletion       : 0.00
% 15.12/6.79  Index Matching       : 0.00
% 15.12/6.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
