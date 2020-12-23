%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:25 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 465 expanded)
%              Number of leaves         :   26 ( 170 expanded)
%              Depth                    :   12
%              Number of atoms          :  416 (1901 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_112,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_86,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(c_40,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1476,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_49,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_60,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_99,plain,(
    ! [A_43,B_44] :
      ( k1_tops_1(A_43,k2_pre_topc(A_43,B_44)) = B_44
      | ~ v6_tops_1(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_112,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50,c_105])).

tff(c_91,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k2_pre_topc(A_41,B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v3_pre_topc(k1_tops_1(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_145,plain,(
    ! [A_51,B_52] :
      ( v3_pre_topc(k1_tops_1(A_51,k2_pre_topc(A_51,B_52)),A_51)
      | ~ v2_pre_topc(A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_91,c_20])).

tff(c_148,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_145])).

tff(c_150,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_34,c_148])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_150])).

tff(c_153,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_157,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_328,plain,(
    ! [A_78,B_79] :
      ( k1_tops_1(A_78,k2_pre_topc(A_78,B_79)) = B_79
      | ~ v6_tops_1(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_334,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_328])).

tff(c_341,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50,c_334])).

tff(c_174,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k2_pre_topc(A_55,B_56),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k1_tops_1(A_13,B_15),B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_352,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k1_tops_1(A_82,k2_pre_topc(A_82,B_83)),k2_pre_topc(A_82,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_174,c_22])).

tff(c_357,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_352])).

tff(c_360,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_357])).

tff(c_160,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tops_1(A_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_164,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_160])).

tff(c_170,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_164])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_182,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_154,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_259,plain,(
    ! [B_71,A_72,C_73] :
      ( r1_tarski(B_71,k1_tops_1(A_72,C_73))
      | ~ r1_tarski(B_71,C_73)
      | ~ v3_pre_topc(B_71,A_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_265,plain,(
    ! [B_71] :
      ( r1_tarski(B_71,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_71,'#skF_3')
      | ~ v3_pre_topc(B_71,'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_259])).

tff(c_288,plain,(
    ! [B_75] :
      ( r1_tarski(B_75,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_75,'#skF_3')
      | ~ v3_pre_topc(B_75,'#skF_1')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_265])).

tff(c_295,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_288])).

tff(c_301,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_6,c_295])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_301])).

tff(c_304,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_467,plain,(
    ! [B_101,A_102] :
      ( v4_tops_1(B_101,A_102)
      | ~ r1_tarski(B_101,k2_pre_topc(A_102,k1_tops_1(A_102,B_101)))
      | ~ r1_tarski(k1_tops_1(A_102,k2_pre_topc(A_102,B_101)),B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_473,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_467])).

tff(c_476,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_6,c_360,c_304,c_473])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_476])).

tff(c_479,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_480,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_38,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_482,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_480,c_38])).

tff(c_483,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(k1_tops_1(A_103,B_104),B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_485,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_483])).

tff(c_490,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_485])).

tff(c_496,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_490,c_2])).

tff(c_500,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_598,plain,(
    ! [B_123,A_124,C_125] :
      ( r1_tarski(B_123,k1_tops_1(A_124,C_125))
      | ~ r1_tarski(B_123,C_125)
      | ~ v3_pre_topc(B_123,A_124)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_602,plain,(
    ! [B_123] :
      ( r1_tarski(B_123,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_123,'#skF_4')
      | ~ v3_pre_topc(B_123,'#skF_2')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_598])).

tff(c_612,plain,(
    ! [B_126] :
      ( r1_tarski(B_126,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_126,'#skF_4')
      | ~ v3_pre_topc(B_126,'#skF_2')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_602])).

tff(c_619,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_612])).

tff(c_625,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_6,c_619])).

tff(c_627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_625])).

tff(c_628,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_834,plain,(
    ! [B_159,A_160] :
      ( r1_tarski(B_159,k2_pre_topc(A_160,k1_tops_1(A_160,B_159)))
      | ~ v4_tops_1(B_159,A_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_845,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_834])).

tff(c_852,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_482,c_845])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_877,plain,(
    ! [B_165,A_166,C_167] :
      ( r1_tarski(B_165,k1_tops_1(A_166,C_167))
      | ~ r1_tarski(B_165,C_167)
      | ~ v3_pre_topc(B_165,A_166)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_945,plain,(
    ! [B_178,A_179,B_180] :
      ( r1_tarski(B_178,k1_tops_1(A_179,k2_pre_topc(A_179,B_180)))
      | ~ r1_tarski(B_178,k2_pre_topc(A_179,B_180))
      | ~ v3_pre_topc(B_178,A_179)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(resolution,[status(thm)],[c_8,c_877])).

tff(c_868,plain,(
    ! [A_163,B_164] :
      ( r1_tarski(k1_tops_1(A_163,k2_pre_topc(A_163,B_164)),B_164)
      | ~ v4_tops_1(B_164,A_163)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_874,plain,(
    ! [A_163,B_164] :
      ( k1_tops_1(A_163,k2_pre_topc(A_163,B_164)) = B_164
      | ~ r1_tarski(B_164,k1_tops_1(A_163,k2_pre_topc(A_163,B_164)))
      | ~ v4_tops_1(B_164,A_163)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_868,c_2])).

tff(c_1046,plain,(
    ! [A_185,B_186] :
      ( k1_tops_1(A_185,k2_pre_topc(A_185,B_186)) = B_186
      | ~ v4_tops_1(B_186,A_185)
      | ~ r1_tarski(B_186,k2_pre_topc(A_185,B_186))
      | ~ v3_pre_topc(B_186,A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_945,c_874])).

tff(c_1048,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_852,c_1046])).

tff(c_1053,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_479,c_482,c_1048])).

tff(c_16,plain,(
    ! [B_10,A_8] :
      ( v6_tops_1(B_10,A_8)
      | k1_tops_1(A_8,k2_pre_topc(A_8,B_10)) != B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1086,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_16])).

tff(c_1109,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_1086])).

tff(c_1111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_1109])).

tff(c_1113,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1114,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1113,c_46])).

tff(c_1112,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1124,plain,(
    ! [A_189,B_190] :
      ( r1_tarski(k1_tops_1(A_189,B_190),B_190)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1126,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1124])).

tff(c_1131,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1126])).

tff(c_1137,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1131,c_2])).

tff(c_1141,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1137])).

tff(c_1206,plain,(
    ! [B_209,A_210,C_211] :
      ( r1_tarski(B_209,k1_tops_1(A_210,C_211))
      | ~ r1_tarski(B_209,C_211)
      | ~ v3_pre_topc(B_209,A_210)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1210,plain,(
    ! [B_209] :
      ( r1_tarski(B_209,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_209,'#skF_4')
      | ~ v3_pre_topc(B_209,'#skF_2')
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_1206])).

tff(c_1220,plain,(
    ! [B_212] :
      ( r1_tarski(B_212,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_212,'#skF_4')
      | ~ v3_pre_topc(B_212,'#skF_2')
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1210])).

tff(c_1227,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1220])).

tff(c_1233,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_6,c_1227])).

tff(c_1235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1141,c_1233])).

tff(c_1236,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1137])).

tff(c_1284,plain,(
    ! [B_225,A_226] :
      ( r1_tarski(B_225,k2_pre_topc(A_226,k1_tops_1(A_226,B_225)))
      | ~ v4_tops_1(B_225,A_226)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1289,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_1284])).

tff(c_1292,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_1112,c_1289])).

tff(c_1317,plain,(
    ! [B_231,A_232,C_233] :
      ( r1_tarski(B_231,k1_tops_1(A_232,C_233))
      | ~ r1_tarski(B_231,C_233)
      | ~ v3_pre_topc(B_231,A_232)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1378,plain,(
    ! [B_245,A_246,B_247] :
      ( r1_tarski(B_245,k1_tops_1(A_246,k2_pre_topc(A_246,B_247)))
      | ~ r1_tarski(B_245,k2_pre_topc(A_246,B_247))
      | ~ v3_pre_topc(B_245,A_246)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(resolution,[status(thm)],[c_8,c_1317])).

tff(c_1297,plain,(
    ! [A_227,B_228] :
      ( r1_tarski(k1_tops_1(A_227,k2_pre_topc(A_227,B_228)),B_228)
      | ~ v4_tops_1(B_228,A_227)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1300,plain,(
    ! [A_227,B_228] :
      ( k1_tops_1(A_227,k2_pre_topc(A_227,B_228)) = B_228
      | ~ r1_tarski(B_228,k1_tops_1(A_227,k2_pre_topc(A_227,B_228)))
      | ~ v4_tops_1(B_228,A_227)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(resolution,[status(thm)],[c_1297,c_2])).

tff(c_1404,plain,(
    ! [A_248,B_249] :
      ( k1_tops_1(A_248,k2_pre_topc(A_248,B_249)) = B_249
      | ~ v4_tops_1(B_249,A_248)
      | ~ r1_tarski(B_249,k2_pre_topc(A_248,B_249))
      | ~ v3_pre_topc(B_249,A_248)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(resolution,[status(thm)],[c_1378,c_1300])).

tff(c_1406,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1292,c_1404])).

tff(c_1409,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_1114,c_1112,c_1406])).

tff(c_1439,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1409,c_16])).

tff(c_1462,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_1439])).

tff(c_1464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_1462])).

tff(c_1465,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1516,plain,(
    ! [A_258,B_259] :
      ( k1_tops_1(A_258,k2_pre_topc(A_258,B_259)) = B_259
      | ~ v6_tops_1(B_259,A_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1522,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1516])).

tff(c_1529,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1465,c_1522])).

tff(c_1502,plain,(
    ! [A_256,B_257] :
      ( v3_pre_topc(k1_tops_1(A_256,B_257),A_256)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1550,plain,(
    ! [A_262,B_263] :
      ( v3_pre_topc(k1_tops_1(A_262,k2_pre_topc(A_262,B_263)),A_262)
      | ~ v2_pre_topc(A_262)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(resolution,[status(thm)],[c_8,c_1502])).

tff(c_1553,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_1550])).

tff(c_1558,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_34,c_1553])).

tff(c_1560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1476,c_1558])).

tff(c_1562,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1561,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1563,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1561])).

tff(c_1774,plain,(
    ! [A_292,B_293] :
      ( k1_tops_1(A_292,k2_pre_topc(A_292,B_293)) = B_293
      | ~ v6_tops_1(B_293,A_292)
      | ~ m1_subset_1(B_293,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1780,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1774])).

tff(c_1787,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1465,c_1780])).

tff(c_1755,plain,(
    ! [A_288,B_289] :
      ( m1_subset_1(k2_pre_topc(A_288,B_289),k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1807,plain,(
    ! [A_296,B_297] :
      ( r1_tarski(k1_tops_1(A_296,k2_pre_topc(A_296,B_297)),k2_pre_topc(A_296,B_297))
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(resolution,[status(thm)],[c_1755,c_22])).

tff(c_1812,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_1807])).

tff(c_1818,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1812])).

tff(c_1568,plain,(
    ! [A_264,B_265] :
      ( r1_tarski(k1_tops_1(A_264,B_265),B_265)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1572,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1568])).

tff(c_1578,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1572])).

tff(c_1584,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1578,c_2])).

tff(c_1586,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1584])).

tff(c_1714,plain,(
    ! [B_284,A_285,C_286] :
      ( r1_tarski(B_284,k1_tops_1(A_285,C_286))
      | ~ r1_tarski(B_284,C_286)
      | ~ v3_pre_topc(B_284,A_285)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1720,plain,(
    ! [B_284] :
      ( r1_tarski(B_284,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_284,'#skF_3')
      | ~ v3_pre_topc(B_284,'#skF_1')
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1714])).

tff(c_1730,plain,(
    ! [B_287] :
      ( r1_tarski(B_287,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_287,'#skF_3')
      | ~ v3_pre_topc(B_287,'#skF_1')
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1720])).

tff(c_1737,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1730])).

tff(c_1743,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_6,c_1737])).

tff(c_1745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1586,c_1743])).

tff(c_1746,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1584])).

tff(c_1964,plain,(
    ! [B_316,A_317] :
      ( v4_tops_1(B_316,A_317)
      | ~ r1_tarski(B_316,k2_pre_topc(A_317,k1_tops_1(A_317,B_316)))
      | ~ r1_tarski(k1_tops_1(A_317,k2_pre_topc(A_317,B_316)),B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ l1_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1970,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_1964])).

tff(c_1976,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_6,c_1818,c_1746,c_1970])).

tff(c_1978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1563,c_1976])).

tff(c_1980,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1561])).

tff(c_1466,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_36,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_1980,c_1466,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:47:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.74  
% 4.20/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.74  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.20/1.74  
% 4.20/1.74  %Foreground sorts:
% 4.20/1.74  
% 4.20/1.74  
% 4.20/1.74  %Background operators:
% 4.20/1.74  
% 4.20/1.74  
% 4.20/1.74  %Foreground operators:
% 4.20/1.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.20/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.74  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 4.20/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.20/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.74  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 4.20/1.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.20/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.20/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.20/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.20/1.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.20/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.74  
% 4.60/1.77  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 4.60/1.77  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 4.60/1.77  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.60/1.77  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.60/1.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.60/1.77  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.60/1.77  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 4.60/1.77  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 4.60/1.77  tff(c_40, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_1476, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 4.60/1.77  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_42, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_49, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 4.60/1.77  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_60, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 4.60/1.77  tff(c_44, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_50, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.60/1.77  tff(c_99, plain, (![A_43, B_44]: (k1_tops_1(A_43, k2_pre_topc(A_43, B_44))=B_44 | ~v6_tops_1(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.60/1.77  tff(c_105, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_99])).
% 4.60/1.77  tff(c_112, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50, c_105])).
% 4.60/1.77  tff(c_91, plain, (![A_41, B_42]: (m1_subset_1(k2_pre_topc(A_41, B_42), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.77  tff(c_20, plain, (![A_11, B_12]: (v3_pre_topc(k1_tops_1(A_11, B_12), A_11) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.60/1.77  tff(c_145, plain, (![A_51, B_52]: (v3_pre_topc(k1_tops_1(A_51, k2_pre_topc(A_51, B_52)), A_51) | ~v2_pre_topc(A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_91, c_20])).
% 4.60/1.77  tff(c_148, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_112, c_145])).
% 4.60/1.77  tff(c_150, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_34, c_148])).
% 4.60/1.77  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_150])).
% 4.60/1.77  tff(c_153, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.60/1.77  tff(c_157, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_153])).
% 4.60/1.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.77  tff(c_328, plain, (![A_78, B_79]: (k1_tops_1(A_78, k2_pre_topc(A_78, B_79))=B_79 | ~v6_tops_1(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.60/1.77  tff(c_334, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_328])).
% 4.60/1.77  tff(c_341, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50, c_334])).
% 4.60/1.77  tff(c_174, plain, (![A_55, B_56]: (m1_subset_1(k2_pre_topc(A_55, B_56), k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.77  tff(c_22, plain, (![A_13, B_15]: (r1_tarski(k1_tops_1(A_13, B_15), B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.77  tff(c_352, plain, (![A_82, B_83]: (r1_tarski(k1_tops_1(A_82, k2_pre_topc(A_82, B_83)), k2_pre_topc(A_82, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_174, c_22])).
% 4.60/1.77  tff(c_357, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_341, c_352])).
% 4.60/1.77  tff(c_360, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_357])).
% 4.60/1.77  tff(c_160, plain, (![A_53, B_54]: (r1_tarski(k1_tops_1(A_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.77  tff(c_164, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_160])).
% 4.60/1.77  tff(c_170, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_164])).
% 4.60/1.77  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.77  tff(c_180, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_170, c_2])).
% 4.60/1.77  tff(c_182, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_180])).
% 4.60/1.77  tff(c_154, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 4.60/1.77  tff(c_259, plain, (![B_71, A_72, C_73]: (r1_tarski(B_71, k1_tops_1(A_72, C_73)) | ~r1_tarski(B_71, C_73) | ~v3_pre_topc(B_71, A_72) | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.60/1.77  tff(c_265, plain, (![B_71]: (r1_tarski(B_71, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_71, '#skF_3') | ~v3_pre_topc(B_71, '#skF_1') | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_259])).
% 4.60/1.77  tff(c_288, plain, (![B_75]: (r1_tarski(B_75, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_75, '#skF_3') | ~v3_pre_topc(B_75, '#skF_1') | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_265])).
% 4.60/1.77  tff(c_295, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_288])).
% 4.60/1.77  tff(c_301, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_6, c_295])).
% 4.60/1.77  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_301])).
% 4.60/1.77  tff(c_304, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_180])).
% 4.60/1.77  tff(c_467, plain, (![B_101, A_102]: (v4_tops_1(B_101, A_102) | ~r1_tarski(B_101, k2_pre_topc(A_102, k1_tops_1(A_102, B_101))) | ~r1_tarski(k1_tops_1(A_102, k2_pre_topc(A_102, B_101)), B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.77  tff(c_473, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_341, c_467])).
% 4.60/1.77  tff(c_476, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_6, c_360, c_304, c_473])).
% 4.60/1.77  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_476])).
% 4.60/1.77  tff(c_479, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_153])).
% 4.60/1.77  tff(c_480, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_153])).
% 4.60/1.77  tff(c_38, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_482, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_480, c_38])).
% 4.60/1.77  tff(c_483, plain, (![A_103, B_104]: (r1_tarski(k1_tops_1(A_103, B_104), B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.77  tff(c_485, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_483])).
% 4.60/1.77  tff(c_490, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_485])).
% 4.60/1.77  tff(c_496, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_490, c_2])).
% 4.60/1.77  tff(c_500, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_496])).
% 4.60/1.77  tff(c_598, plain, (![B_123, A_124, C_125]: (r1_tarski(B_123, k1_tops_1(A_124, C_125)) | ~r1_tarski(B_123, C_125) | ~v3_pre_topc(B_123, A_124) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.60/1.77  tff(c_602, plain, (![B_123]: (r1_tarski(B_123, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_123, '#skF_4') | ~v3_pre_topc(B_123, '#skF_2') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_598])).
% 4.60/1.77  tff(c_612, plain, (![B_126]: (r1_tarski(B_126, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_126, '#skF_4') | ~v3_pre_topc(B_126, '#skF_2') | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_602])).
% 4.60/1.77  tff(c_619, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_612])).
% 4.60/1.77  tff(c_625, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_6, c_619])).
% 4.60/1.77  tff(c_627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_500, c_625])).
% 4.60/1.77  tff(c_628, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_496])).
% 4.60/1.77  tff(c_834, plain, (![B_159, A_160]: (r1_tarski(B_159, k2_pre_topc(A_160, k1_tops_1(A_160, B_159))) | ~v4_tops_1(B_159, A_160) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.77  tff(c_845, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_628, c_834])).
% 4.60/1.77  tff(c_852, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_482, c_845])).
% 4.60/1.77  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.77  tff(c_877, plain, (![B_165, A_166, C_167]: (r1_tarski(B_165, k1_tops_1(A_166, C_167)) | ~r1_tarski(B_165, C_167) | ~v3_pre_topc(B_165, A_166) | ~m1_subset_1(C_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.60/1.77  tff(c_945, plain, (![B_178, A_179, B_180]: (r1_tarski(B_178, k1_tops_1(A_179, k2_pre_topc(A_179, B_180))) | ~r1_tarski(B_178, k2_pre_topc(A_179, B_180)) | ~v3_pre_topc(B_178, A_179) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(resolution, [status(thm)], [c_8, c_877])).
% 4.60/1.77  tff(c_868, plain, (![A_163, B_164]: (r1_tarski(k1_tops_1(A_163, k2_pre_topc(A_163, B_164)), B_164) | ~v4_tops_1(B_164, A_163) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.77  tff(c_874, plain, (![A_163, B_164]: (k1_tops_1(A_163, k2_pre_topc(A_163, B_164))=B_164 | ~r1_tarski(B_164, k1_tops_1(A_163, k2_pre_topc(A_163, B_164))) | ~v4_tops_1(B_164, A_163) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_868, c_2])).
% 4.60/1.77  tff(c_1046, plain, (![A_185, B_186]: (k1_tops_1(A_185, k2_pre_topc(A_185, B_186))=B_186 | ~v4_tops_1(B_186, A_185) | ~r1_tarski(B_186, k2_pre_topc(A_185, B_186)) | ~v3_pre_topc(B_186, A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(resolution, [status(thm)], [c_945, c_874])).
% 4.60/1.77  tff(c_1048, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_852, c_1046])).
% 4.60/1.77  tff(c_1053, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_479, c_482, c_1048])).
% 4.60/1.77  tff(c_16, plain, (![B_10, A_8]: (v6_tops_1(B_10, A_8) | k1_tops_1(A_8, k2_pre_topc(A_8, B_10))!=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.60/1.77  tff(c_1086, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1053, c_16])).
% 4.60/1.77  tff(c_1109, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_1086])).
% 4.60/1.77  tff(c_1111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_1109])).
% 4.60/1.77  tff(c_1113, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.60/1.77  tff(c_46, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_1114, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1113, c_46])).
% 4.60/1.77  tff(c_1112, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.60/1.77  tff(c_1124, plain, (![A_189, B_190]: (r1_tarski(k1_tops_1(A_189, B_190), B_190) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.77  tff(c_1126, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_1124])).
% 4.60/1.77  tff(c_1131, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1126])).
% 4.60/1.77  tff(c_1137, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_1131, c_2])).
% 4.60/1.77  tff(c_1141, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1137])).
% 4.60/1.77  tff(c_1206, plain, (![B_209, A_210, C_211]: (r1_tarski(B_209, k1_tops_1(A_210, C_211)) | ~r1_tarski(B_209, C_211) | ~v3_pre_topc(B_209, A_210) | ~m1_subset_1(C_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.60/1.77  tff(c_1210, plain, (![B_209]: (r1_tarski(B_209, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_209, '#skF_4') | ~v3_pre_topc(B_209, '#skF_2') | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_1206])).
% 4.60/1.77  tff(c_1220, plain, (![B_212]: (r1_tarski(B_212, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_212, '#skF_4') | ~v3_pre_topc(B_212, '#skF_2') | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1210])).
% 4.60/1.77  tff(c_1227, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_1220])).
% 4.60/1.77  tff(c_1233, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_6, c_1227])).
% 4.60/1.77  tff(c_1235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1141, c_1233])).
% 4.60/1.77  tff(c_1236, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1137])).
% 4.60/1.77  tff(c_1284, plain, (![B_225, A_226]: (r1_tarski(B_225, k2_pre_topc(A_226, k1_tops_1(A_226, B_225))) | ~v4_tops_1(B_225, A_226) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.77  tff(c_1289, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1236, c_1284])).
% 4.60/1.77  tff(c_1292, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_1112, c_1289])).
% 4.60/1.77  tff(c_1317, plain, (![B_231, A_232, C_233]: (r1_tarski(B_231, k1_tops_1(A_232, C_233)) | ~r1_tarski(B_231, C_233) | ~v3_pre_topc(B_231, A_232) | ~m1_subset_1(C_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.60/1.77  tff(c_1378, plain, (![B_245, A_246, B_247]: (r1_tarski(B_245, k1_tops_1(A_246, k2_pre_topc(A_246, B_247))) | ~r1_tarski(B_245, k2_pre_topc(A_246, B_247)) | ~v3_pre_topc(B_245, A_246) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_246))) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246))), inference(resolution, [status(thm)], [c_8, c_1317])).
% 4.60/1.77  tff(c_1297, plain, (![A_227, B_228]: (r1_tarski(k1_tops_1(A_227, k2_pre_topc(A_227, B_228)), B_228) | ~v4_tops_1(B_228, A_227) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.77  tff(c_1300, plain, (![A_227, B_228]: (k1_tops_1(A_227, k2_pre_topc(A_227, B_228))=B_228 | ~r1_tarski(B_228, k1_tops_1(A_227, k2_pre_topc(A_227, B_228))) | ~v4_tops_1(B_228, A_227) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(resolution, [status(thm)], [c_1297, c_2])).
% 4.60/1.77  tff(c_1404, plain, (![A_248, B_249]: (k1_tops_1(A_248, k2_pre_topc(A_248, B_249))=B_249 | ~v4_tops_1(B_249, A_248) | ~r1_tarski(B_249, k2_pre_topc(A_248, B_249)) | ~v3_pre_topc(B_249, A_248) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(resolution, [status(thm)], [c_1378, c_1300])).
% 4.60/1.77  tff(c_1406, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1292, c_1404])).
% 4.60/1.77  tff(c_1409, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_1114, c_1112, c_1406])).
% 4.60/1.77  tff(c_1439, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1409, c_16])).
% 4.60/1.77  tff(c_1462, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_1439])).
% 4.60/1.77  tff(c_1464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_1462])).
% 4.60/1.77  tff(c_1465, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.60/1.77  tff(c_1516, plain, (![A_258, B_259]: (k1_tops_1(A_258, k2_pre_topc(A_258, B_259))=B_259 | ~v6_tops_1(B_259, A_258) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.60/1.77  tff(c_1522, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1516])).
% 4.60/1.77  tff(c_1529, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1465, c_1522])).
% 4.60/1.77  tff(c_1502, plain, (![A_256, B_257]: (v3_pre_topc(k1_tops_1(A_256, B_257), A_256) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.60/1.77  tff(c_1550, plain, (![A_262, B_263]: (v3_pre_topc(k1_tops_1(A_262, k2_pre_topc(A_262, B_263)), A_262) | ~v2_pre_topc(A_262) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(resolution, [status(thm)], [c_8, c_1502])).
% 4.60/1.77  tff(c_1553, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1529, c_1550])).
% 4.60/1.77  tff(c_1558, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_34, c_1553])).
% 4.60/1.77  tff(c_1560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1476, c_1558])).
% 4.60/1.77  tff(c_1562, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 4.60/1.77  tff(c_1561, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.60/1.77  tff(c_1563, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1561])).
% 4.60/1.77  tff(c_1774, plain, (![A_292, B_293]: (k1_tops_1(A_292, k2_pre_topc(A_292, B_293))=B_293 | ~v6_tops_1(B_293, A_292) | ~m1_subset_1(B_293, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.60/1.77  tff(c_1780, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1774])).
% 4.60/1.77  tff(c_1787, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1465, c_1780])).
% 4.60/1.77  tff(c_1755, plain, (![A_288, B_289]: (m1_subset_1(k2_pre_topc(A_288, B_289), k1_zfmisc_1(u1_struct_0(A_288))) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.77  tff(c_1807, plain, (![A_296, B_297]: (r1_tarski(k1_tops_1(A_296, k2_pre_topc(A_296, B_297)), k2_pre_topc(A_296, B_297)) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_pre_topc(A_296))), inference(resolution, [status(thm)], [c_1755, c_22])).
% 4.60/1.77  tff(c_1812, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1787, c_1807])).
% 4.60/1.77  tff(c_1818, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1812])).
% 4.60/1.77  tff(c_1568, plain, (![A_264, B_265]: (r1_tarski(k1_tops_1(A_264, B_265), B_265) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.77  tff(c_1572, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1568])).
% 4.60/1.77  tff(c_1578, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1572])).
% 4.60/1.77  tff(c_1584, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1578, c_2])).
% 4.60/1.77  tff(c_1586, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1584])).
% 4.60/1.77  tff(c_1714, plain, (![B_284, A_285, C_286]: (r1_tarski(B_284, k1_tops_1(A_285, C_286)) | ~r1_tarski(B_284, C_286) | ~v3_pre_topc(B_284, A_285) | ~m1_subset_1(C_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(A_285))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.60/1.77  tff(c_1720, plain, (![B_284]: (r1_tarski(B_284, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_284, '#skF_3') | ~v3_pre_topc(B_284, '#skF_1') | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1714])).
% 4.60/1.77  tff(c_1730, plain, (![B_287]: (r1_tarski(B_287, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_287, '#skF_3') | ~v3_pre_topc(B_287, '#skF_1') | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1720])).
% 4.60/1.77  tff(c_1737, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_1730])).
% 4.60/1.77  tff(c_1743, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1562, c_6, c_1737])).
% 4.60/1.77  tff(c_1745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1586, c_1743])).
% 4.60/1.77  tff(c_1746, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1584])).
% 4.60/1.77  tff(c_1964, plain, (![B_316, A_317]: (v4_tops_1(B_316, A_317) | ~r1_tarski(B_316, k2_pre_topc(A_317, k1_tops_1(A_317, B_316))) | ~r1_tarski(k1_tops_1(A_317, k2_pre_topc(A_317, B_316)), B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_317))) | ~l1_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.77  tff(c_1970, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1787, c_1964])).
% 4.60/1.77  tff(c_1976, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_6, c_1818, c_1746, c_1970])).
% 4.60/1.77  tff(c_1978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1563, c_1976])).
% 4.60/1.77  tff(c_1980, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1561])).
% 4.60/1.77  tff(c_1466, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.60/1.77  tff(c_36, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.77  tff(c_1984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1562, c_1980, c_1466, c_36])).
% 4.60/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.77  
% 4.60/1.77  Inference rules
% 4.60/1.77  ----------------------
% 4.60/1.77  #Ref     : 0
% 4.60/1.77  #Sup     : 390
% 4.60/1.77  #Fact    : 0
% 4.60/1.77  #Define  : 0
% 4.60/1.77  #Split   : 58
% 4.60/1.77  #Chain   : 0
% 4.60/1.77  #Close   : 0
% 4.60/1.77  
% 4.60/1.77  Ordering : KBO
% 4.60/1.77  
% 4.60/1.77  Simplification rules
% 4.60/1.77  ----------------------
% 4.60/1.77  #Subsume      : 38
% 4.60/1.77  #Demod        : 525
% 4.60/1.77  #Tautology    : 135
% 4.60/1.77  #SimpNegUnit  : 17
% 4.60/1.77  #BackRed      : 5
% 4.60/1.77  
% 4.60/1.77  #Partial instantiations: 0
% 4.60/1.77  #Strategies tried      : 1
% 4.60/1.77  
% 4.60/1.77  Timing (in seconds)
% 4.60/1.77  ----------------------
% 4.60/1.77  Preprocessing        : 0.31
% 4.60/1.77  Parsing              : 0.17
% 4.60/1.77  CNF conversion       : 0.02
% 4.60/1.77  Main loop            : 0.67
% 4.60/1.77  Inferencing          : 0.24
% 4.60/1.77  Reduction            : 0.21
% 4.60/1.77  Demodulation         : 0.14
% 4.60/1.77  BG Simplification    : 0.03
% 4.60/1.77  Subsumption          : 0.13
% 4.60/1.77  Abstraction          : 0.03
% 4.60/1.77  MUC search           : 0.00
% 4.60/1.77  Cooper               : 0.00
% 4.60/1.77  Total                : 1.05
% 4.60/1.77  Index Insertion      : 0.00
% 4.60/1.77  Index Deletion       : 0.00
% 4.60/1.77  Index Matching       : 0.00
% 4.60/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
