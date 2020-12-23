%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:22 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 622 expanded)
%              Number of leaves         :   27 ( 222 expanded)
%              Depth                    :   15
%              Number of atoms          :  425 (2578 expanded)
%              Number of equality atoms :   46 ( 118 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_118,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_92,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(c_42,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1515,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_51,plain,(
    ~ v5_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_62,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_124,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,k1_tops_1(A_49,B_50)) = B_50
      | ~ v5_tops_1(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_134,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_52,c_128])).

tff(c_93,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k1_tops_1(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( v4_pre_topc(k2_pre_topc(A_13,B_14),A_13)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_170,plain,(
    ! [A_55,B_56] :
      ( v4_pre_topc(k2_pre_topc(A_55,k1_tops_1(A_55,B_56)),A_55)
      | ~ v2_pre_topc(A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_93,c_22])).

tff(c_173,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_170])).

tff(c_175,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_173])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_175])).

tff(c_178,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_182,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_185,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k1_tops_1(A_57,B_58),B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_187,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_192,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_187])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,(
    ! [A_67,B_68] :
      ( k2_pre_topc(A_67,k1_tops_1(A_67,B_68)) = B_68
      | ~ v5_tops_1(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_250,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_246])).

tff(c_256,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_52,c_250])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k1_tops_1(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_223,plain,(
    ! [A_63,B_64] :
      ( k2_pre_topc(A_63,k2_pre_topc(A_63,B_64)) = k2_pre_topc(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_354,plain,(
    ! [A_82,B_83] :
      ( k2_pre_topc(A_82,k2_pre_topc(A_82,k1_tops_1(A_82,B_83))) = k2_pre_topc(A_82,k1_tops_1(A_82,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_20,c_223])).

tff(c_358,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_354])).

tff(c_364,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_256,c_256,c_358])).

tff(c_179,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_307,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(k2_pre_topc(A_77,C_78),B_79)
      | ~ r1_tarski(C_78,B_79)
      | ~ v4_pre_topc(B_79,A_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_311,plain,(
    ! [B_79] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),B_79)
      | ~ r1_tarski('#skF_3',B_79)
      | ~ v4_pre_topc(B_79,'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_307])).

tff(c_321,plain,(
    ! [B_80] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),B_80)
      | ~ r1_tarski('#skF_3',B_80)
      | ~ v4_pre_topc(B_80,'#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_311])).

tff(c_328,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_321])).

tff(c_334,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_6,c_328])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_337,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_338,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_368,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_338])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_368])).

tff(c_376,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_10,plain,(
    ! [B_7,A_5] :
      ( v4_tops_1(B_7,A_5)
      | ~ r1_tarski(B_7,k2_pre_topc(A_5,k1_tops_1(A_5,B_7)))
      | ~ r1_tarski(k1_tops_1(A_5,k2_pre_topc(A_5,B_7)),B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_407,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_10])).

tff(c_414,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_192,c_6,c_256,c_407])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_414])).

tff(c_417,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_418,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_40,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_420,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_418,c_40])).

tff(c_421,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_tops_1(A_86,B_87),B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_425,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_421])).

tff(c_431,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_425])).

tff(c_578,plain,(
    ! [A_108,C_109,B_110] :
      ( r1_tarski(k2_pre_topc(A_108,C_109),B_110)
      | ~ r1_tarski(C_109,B_110)
      | ~ v4_pre_topc(B_110,A_108)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_720,plain,(
    ! [A_123,B_124,B_125] :
      ( r1_tarski(k2_pre_topc(A_123,k1_tops_1(A_123,B_124)),B_125)
      | ~ r1_tarski(k1_tops_1(A_123,B_124),B_125)
      | ~ v4_pre_topc(B_125,A_123)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_20,c_578])).

tff(c_511,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(B_100,k2_pre_topc(A_101,k1_tops_1(A_101,B_100)))
      | ~ v4_tops_1(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_517,plain,(
    ! [A_101,B_100] :
      ( k2_pre_topc(A_101,k1_tops_1(A_101,B_100)) = B_100
      | ~ r1_tarski(k2_pre_topc(A_101,k1_tops_1(A_101,B_100)),B_100)
      | ~ v4_tops_1(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_511,c_2])).

tff(c_875,plain,(
    ! [A_132,B_133] :
      ( k2_pre_topc(A_132,k1_tops_1(A_132,B_133)) = B_133
      | ~ v4_tops_1(B_133,A_132)
      | ~ r1_tarski(k1_tops_1(A_132,B_133),B_133)
      | ~ v4_pre_topc(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_720,c_517])).

tff(c_881,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_431,c_875])).

tff(c_890,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_417,c_420,c_881])).

tff(c_16,plain,(
    ! [B_10,A_8] :
      ( v5_tops_1(B_10,A_8)
      | k2_pre_topc(A_8,k1_tops_1(A_8,B_10)) != B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_918,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_16])).

tff(c_937,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_918])).

tff(c_939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_937])).

tff(c_940,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_952,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(k1_tops_1(A_136,B_137),B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_956,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_952])).

tff(c_962,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_956])).

tff(c_1050,plain,(
    ! [A_156,C_157,B_158] :
      ( r1_tarski(k2_pre_topc(A_156,C_157),B_158)
      | ~ r1_tarski(C_157,B_158)
      | ~ v4_pre_topc(B_158,A_156)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1433,plain,(
    ! [A_195,B_196,B_197] :
      ( r1_tarski(k2_pre_topc(A_195,k1_tops_1(A_195,B_196)),B_197)
      | ~ r1_tarski(k1_tops_1(A_195,B_196),B_197)
      | ~ v4_pre_topc(B_197,A_195)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195) ) ),
    inference(resolution,[status(thm)],[c_20,c_1050])).

tff(c_941,plain,(
    ~ v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_942,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_941,c_46])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( r1_tarski(B_7,k2_pre_topc(A_5,k1_tops_1(A_5,B_7)))
      | ~ v4_tops_1(B_7,A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1363,plain,(
    ! [A_188,B_189,B_190] :
      ( r1_tarski(k2_pre_topc(A_188,k1_tops_1(A_188,B_189)),B_190)
      | ~ r1_tarski(k1_tops_1(A_188,B_189),B_190)
      | ~ v4_pre_topc(B_190,A_188)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(resolution,[status(thm)],[c_20,c_1050])).

tff(c_1032,plain,(
    ! [B_152,A_153] :
      ( r1_tarski(B_152,k2_pre_topc(A_153,k1_tops_1(A_153,B_152)))
      | ~ v4_tops_1(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1035,plain,(
    ! [A_153,B_152] :
      ( k2_pre_topc(A_153,k1_tops_1(A_153,B_152)) = B_152
      | ~ r1_tarski(k2_pre_topc(A_153,k1_tops_1(A_153,B_152)),B_152)
      | ~ v4_tops_1(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(resolution,[status(thm)],[c_1032,c_2])).

tff(c_1383,plain,(
    ! [A_191,B_192] :
      ( k2_pre_topc(A_191,k1_tops_1(A_191,B_192)) = B_192
      | ~ v4_tops_1(B_192,A_191)
      | ~ r1_tarski(k1_tops_1(A_191,B_192),B_192)
      | ~ v4_pre_topc(B_192,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_1363,c_1035])).

tff(c_1389,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_962,c_1383])).

tff(c_1398,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_940,c_942,c_1389])).

tff(c_1236,plain,(
    ! [A_177,B_178,B_179] :
      ( r1_tarski(k2_pre_topc(A_177,k1_tops_1(A_177,B_178)),B_179)
      | ~ r1_tarski(k1_tops_1(A_177,B_178),B_179)
      | ~ v4_pre_topc(B_179,A_177)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_20,c_1050])).

tff(c_1250,plain,(
    ! [A_180,B_181] :
      ( k2_pre_topc(A_180,k1_tops_1(A_180,B_181)) = B_181
      | ~ v4_tops_1(B_181,A_180)
      | ~ r1_tarski(k1_tops_1(A_180,B_181),B_181)
      | ~ v4_pre_topc(B_181,A_180)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_1236,c_1035])).

tff(c_1254,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_962,c_1250])).

tff(c_1260,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_940,c_942,c_1254])).

tff(c_990,plain,(
    ! [A_142,B_143] :
      ( k2_pre_topc(A_142,k2_pre_topc(A_142,B_143)) = k2_pre_topc(A_142,B_143)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1097,plain,(
    ! [A_161,B_162] :
      ( k2_pre_topc(A_161,k2_pre_topc(A_161,k1_tops_1(A_161,B_162))) = k2_pre_topc(A_161,k1_tops_1(A_161,B_162))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_20,c_990])).

tff(c_1103,plain,
    ( k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1097])).

tff(c_1110,plain,(
    k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1103])).

tff(c_14,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_tops_1(A_5,k2_pre_topc(A_5,B_7)),B_7)
      | ~ v4_tops_1(B_7,A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1146,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))),k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')))
    | ~ v4_tops_1(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_14])).

tff(c_1152,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))),k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')))
    | ~ v4_tops_1(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1146])).

tff(c_1215,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1152])).

tff(c_1264,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_1215])).

tff(c_1268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1264])).

tff(c_1270,plain,(
    m1_subset_1(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1152])).

tff(c_1056,plain,(
    ! [B_158] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),B_158)
      | ~ r1_tarski('#skF_4',B_158)
      | ~ v4_pre_topc(B_158,'#skF_2')
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_1050])).

tff(c_1063,plain,(
    ! [B_158] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),B_158)
      | ~ r1_tarski('#skF_4',B_158)
      | ~ v4_pre_topc(B_158,'#skF_2')
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1056])).

tff(c_1294,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')))
    | ~ v4_pre_topc(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1270,c_1063])).

tff(c_1313,plain,(
    ~ v4_pre_topc(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1294])).

tff(c_1405,plain,(
    ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1313])).

tff(c_1411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_1405])).

tff(c_1412,plain,
    ( ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')))
    | r1_tarski(k2_pre_topc('#skF_2','#skF_4'),k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1294])).

tff(c_1415,plain,(
    ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1412])).

tff(c_1418,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1415])).

tff(c_1422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_942,c_1418])).

tff(c_1424,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1412])).

tff(c_1428,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1424,c_2])).

tff(c_1432,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1428])).

tff(c_1436,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1433,c_1432])).

tff(c_1450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_940,c_962,c_1436])).

tff(c_1451,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1428])).

tff(c_1484,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1451,c_16])).

tff(c_1501,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1484])).

tff(c_1503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_1501])).

tff(c_1504,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1578,plain,(
    ! [A_208,B_209] :
      ( k2_pre_topc(A_208,k1_tops_1(A_208,B_209)) = B_209
      | ~ v5_tops_1(B_209,A_208)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1582,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1578])).

tff(c_1588,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1504,c_1582])).

tff(c_1541,plain,(
    ! [A_204,B_205] :
      ( v4_pre_topc(k2_pre_topc(A_204,B_205),A_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1635,plain,(
    ! [A_214,B_215] :
      ( v4_pre_topc(k2_pre_topc(A_214,k1_tops_1(A_214,B_215)),A_214)
      | ~ v2_pre_topc(A_214)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(resolution,[status(thm)],[c_20,c_1541])).

tff(c_1641,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1588,c_1635])).

tff(c_1645,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_1641])).

tff(c_1647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1515,c_1645])).

tff(c_1649,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1505,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1652,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1505,c_38])).

tff(c_1655,plain,(
    ! [A_216,B_217] :
      ( r1_tarski(k1_tops_1(A_216,B_217),B_217)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1657,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1655])).

tff(c_1662,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1657])).

tff(c_1707,plain,(
    ! [A_224,B_225] :
      ( k2_pre_topc(A_224,k1_tops_1(A_224,B_225)) = B_225
      | ~ v5_tops_1(B_225,A_224)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1711,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1707])).

tff(c_1717,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1504,c_1711])).

tff(c_1693,plain,(
    ! [A_222,B_223] :
      ( k2_pre_topc(A_222,k2_pre_topc(A_222,B_223)) = k2_pre_topc(A_222,B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1848,plain,(
    ! [A_241,B_242] :
      ( k2_pre_topc(A_241,k2_pre_topc(A_241,k1_tops_1(A_241,B_242))) = k2_pre_topc(A_241,k1_tops_1(A_241,B_242))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_20,c_1693])).

tff(c_1852,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1848])).

tff(c_1858,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1717,c_1717,c_1852])).

tff(c_1801,plain,(
    ! [A_236,C_237,B_238] :
      ( r1_tarski(k2_pre_topc(A_236,C_237),B_238)
      | ~ r1_tarski(C_237,B_238)
      | ~ v4_pre_topc(B_238,A_236)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1805,plain,(
    ! [B_238] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),B_238)
      | ~ r1_tarski('#skF_3',B_238)
      | ~ v4_pre_topc(B_238,'#skF_1')
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1801])).

tff(c_1815,plain,(
    ! [B_239] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),B_239)
      | ~ r1_tarski('#skF_3',B_239)
      | ~ v4_pre_topc(B_239,'#skF_1')
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1805])).

tff(c_1822,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1815])).

tff(c_1828,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_6,c_1822])).

tff(c_1831,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1828,c_2])).

tff(c_1832,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1831])).

tff(c_1862,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1858,c_1832])).

tff(c_1869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1862])).

tff(c_1870,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1831])).

tff(c_1906,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1870,c_10])).

tff(c_1913,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1662,c_6,c_1717,c_1906])).

tff(c_1915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1652,c_1913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 15:54:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.73  
% 4.14/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.73  %$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.14/1.73  
% 4.14/1.73  %Foreground sorts:
% 4.14/1.73  
% 4.14/1.73  
% 4.14/1.73  %Background operators:
% 4.14/1.73  
% 4.14/1.73  
% 4.14/1.73  %Foreground operators:
% 4.14/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.14/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.73  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 4.14/1.73  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.14/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.14/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.14/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.73  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.14/1.73  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 4.14/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.14/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.14/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.14/1.73  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.14/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.73  
% 4.55/1.80  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v4_pre_topc(D, B) & v4_tops_1(D, B)) => v5_tops_1(D, B)) & (v5_tops_1(C, A) => (v4_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tops_1)).
% 4.55/1.80  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 4.55/1.80  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.55/1.80  tff(f_71, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.55/1.80  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.55/1.80  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.55/1.80  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 4.55/1.80  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 4.55/1.80  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 4.55/1.80  tff(c_42, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_1515, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.55/1.80  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_44, plain, (~v5_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_51, plain, (~v5_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 4.55/1.80  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_62, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.55/1.80  tff(c_48, plain, (v4_pre_topc('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_52, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 4.55/1.80  tff(c_124, plain, (![A_49, B_50]: (k2_pre_topc(A_49, k1_tops_1(A_49, B_50))=B_50 | ~v5_tops_1(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.55/1.80  tff(c_128, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_124])).
% 4.55/1.80  tff(c_134, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_52, c_128])).
% 4.55/1.80  tff(c_93, plain, (![A_43, B_44]: (m1_subset_1(k1_tops_1(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.80  tff(c_22, plain, (![A_13, B_14]: (v4_pre_topc(k2_pre_topc(A_13, B_14), A_13) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.80  tff(c_170, plain, (![A_55, B_56]: (v4_pre_topc(k2_pre_topc(A_55, k1_tops_1(A_55, B_56)), A_55) | ~v2_pre_topc(A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_93, c_22])).
% 4.55/1.80  tff(c_173, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_134, c_170])).
% 4.55/1.80  tff(c_175, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_36, c_173])).
% 4.55/1.80  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_175])).
% 4.55/1.80  tff(c_178, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.55/1.80  tff(c_182, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_178])).
% 4.55/1.80  tff(c_185, plain, (![A_57, B_58]: (r1_tarski(k1_tops_1(A_57, B_58), B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.55/1.80  tff(c_187, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_185])).
% 4.55/1.80  tff(c_192, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_187])).
% 4.55/1.80  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.80  tff(c_246, plain, (![A_67, B_68]: (k2_pre_topc(A_67, k1_tops_1(A_67, B_68))=B_68 | ~v5_tops_1(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.55/1.80  tff(c_250, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_246])).
% 4.55/1.80  tff(c_256, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_52, c_250])).
% 4.55/1.80  tff(c_20, plain, (![A_11, B_12]: (m1_subset_1(k1_tops_1(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.80  tff(c_223, plain, (![A_63, B_64]: (k2_pre_topc(A_63, k2_pre_topc(A_63, B_64))=k2_pre_topc(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.80  tff(c_354, plain, (![A_82, B_83]: (k2_pre_topc(A_82, k2_pre_topc(A_82, k1_tops_1(A_82, B_83)))=k2_pre_topc(A_82, k1_tops_1(A_82, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_20, c_223])).
% 4.55/1.80  tff(c_358, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_354])).
% 4.55/1.80  tff(c_364, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_256, c_256, c_358])).
% 4.55/1.80  tff(c_179, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.55/1.80  tff(c_307, plain, (![A_77, C_78, B_79]: (r1_tarski(k2_pre_topc(A_77, C_78), B_79) | ~r1_tarski(C_78, B_79) | ~v4_pre_topc(B_79, A_77) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.80  tff(c_311, plain, (![B_79]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), B_79) | ~r1_tarski('#skF_3', B_79) | ~v4_pre_topc(B_79, '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_307])).
% 4.55/1.80  tff(c_321, plain, (![B_80]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), B_80) | ~r1_tarski('#skF_3', B_80) | ~v4_pre_topc(B_80, '#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_311])).
% 4.55/1.80  tff(c_328, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_321])).
% 4.55/1.80  tff(c_334, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_6, c_328])).
% 4.55/1.80  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.80  tff(c_337, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_334, c_2])).
% 4.55/1.80  tff(c_338, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_337])).
% 4.55/1.80  tff(c_368, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_338])).
% 4.55/1.80  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_368])).
% 4.55/1.80  tff(c_376, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_337])).
% 4.55/1.80  tff(c_10, plain, (![B_7, A_5]: (v4_tops_1(B_7, A_5) | ~r1_tarski(B_7, k2_pre_topc(A_5, k1_tops_1(A_5, B_7))) | ~r1_tarski(k1_tops_1(A_5, k2_pre_topc(A_5, B_7)), B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/1.80  tff(c_407, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_376, c_10])).
% 4.55/1.80  tff(c_414, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_192, c_6, c_256, c_407])).
% 4.55/1.80  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_414])).
% 4.55/1.80  tff(c_417, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 4.55/1.80  tff(c_418, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_178])).
% 4.55/1.80  tff(c_40, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_420, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_418, c_40])).
% 4.55/1.80  tff(c_421, plain, (![A_86, B_87]: (r1_tarski(k1_tops_1(A_86, B_87), B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.55/1.80  tff(c_425, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_421])).
% 4.55/1.80  tff(c_431, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_425])).
% 4.55/1.80  tff(c_578, plain, (![A_108, C_109, B_110]: (r1_tarski(k2_pre_topc(A_108, C_109), B_110) | ~r1_tarski(C_109, B_110) | ~v4_pre_topc(B_110, A_108) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.80  tff(c_720, plain, (![A_123, B_124, B_125]: (r1_tarski(k2_pre_topc(A_123, k1_tops_1(A_123, B_124)), B_125) | ~r1_tarski(k1_tops_1(A_123, B_124), B_125) | ~v4_pre_topc(B_125, A_123) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_20, c_578])).
% 4.55/1.80  tff(c_511, plain, (![B_100, A_101]: (r1_tarski(B_100, k2_pre_topc(A_101, k1_tops_1(A_101, B_100))) | ~v4_tops_1(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/1.80  tff(c_517, plain, (![A_101, B_100]: (k2_pre_topc(A_101, k1_tops_1(A_101, B_100))=B_100 | ~r1_tarski(k2_pre_topc(A_101, k1_tops_1(A_101, B_100)), B_100) | ~v4_tops_1(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_511, c_2])).
% 4.55/1.80  tff(c_875, plain, (![A_132, B_133]: (k2_pre_topc(A_132, k1_tops_1(A_132, B_133))=B_133 | ~v4_tops_1(B_133, A_132) | ~r1_tarski(k1_tops_1(A_132, B_133), B_133) | ~v4_pre_topc(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_720, c_517])).
% 4.55/1.80  tff(c_881, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_431, c_875])).
% 4.55/1.80  tff(c_890, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_417, c_420, c_881])).
% 4.55/1.80  tff(c_16, plain, (![B_10, A_8]: (v5_tops_1(B_10, A_8) | k2_pre_topc(A_8, k1_tops_1(A_8, B_10))!=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.55/1.80  tff(c_918, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_890, c_16])).
% 4.55/1.80  tff(c_937, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_918])).
% 4.55/1.80  tff(c_939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_937])).
% 4.55/1.80  tff(c_940, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.55/1.80  tff(c_952, plain, (![A_136, B_137]: (r1_tarski(k1_tops_1(A_136, B_137), B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.55/1.80  tff(c_956, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_952])).
% 4.55/1.80  tff(c_962, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_956])).
% 4.55/1.80  tff(c_1050, plain, (![A_156, C_157, B_158]: (r1_tarski(k2_pre_topc(A_156, C_157), B_158) | ~r1_tarski(C_157, B_158) | ~v4_pre_topc(B_158, A_156) | ~m1_subset_1(C_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.80  tff(c_1433, plain, (![A_195, B_196, B_197]: (r1_tarski(k2_pre_topc(A_195, k1_tops_1(A_195, B_196)), B_197) | ~r1_tarski(k1_tops_1(A_195, B_196), B_197) | ~v4_pre_topc(B_197, A_195) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195))), inference(resolution, [status(thm)], [c_20, c_1050])).
% 4.55/1.80  tff(c_941, plain, (~v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.55/1.80  tff(c_46, plain, (v4_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_942, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_941, c_46])).
% 4.55/1.80  tff(c_12, plain, (![B_7, A_5]: (r1_tarski(B_7, k2_pre_topc(A_5, k1_tops_1(A_5, B_7))) | ~v4_tops_1(B_7, A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/1.80  tff(c_1363, plain, (![A_188, B_189, B_190]: (r1_tarski(k2_pre_topc(A_188, k1_tops_1(A_188, B_189)), B_190) | ~r1_tarski(k1_tops_1(A_188, B_189), B_190) | ~v4_pre_topc(B_190, A_188) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(resolution, [status(thm)], [c_20, c_1050])).
% 4.55/1.80  tff(c_1032, plain, (![B_152, A_153]: (r1_tarski(B_152, k2_pre_topc(A_153, k1_tops_1(A_153, B_152))) | ~v4_tops_1(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/1.80  tff(c_1035, plain, (![A_153, B_152]: (k2_pre_topc(A_153, k1_tops_1(A_153, B_152))=B_152 | ~r1_tarski(k2_pre_topc(A_153, k1_tops_1(A_153, B_152)), B_152) | ~v4_tops_1(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(resolution, [status(thm)], [c_1032, c_2])).
% 4.55/1.80  tff(c_1383, plain, (![A_191, B_192]: (k2_pre_topc(A_191, k1_tops_1(A_191, B_192))=B_192 | ~v4_tops_1(B_192, A_191) | ~r1_tarski(k1_tops_1(A_191, B_192), B_192) | ~v4_pre_topc(B_192, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191))), inference(resolution, [status(thm)], [c_1363, c_1035])).
% 4.55/1.80  tff(c_1389, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_962, c_1383])).
% 4.55/1.80  tff(c_1398, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_940, c_942, c_1389])).
% 4.55/1.80  tff(c_1236, plain, (![A_177, B_178, B_179]: (r1_tarski(k2_pre_topc(A_177, k1_tops_1(A_177, B_178)), B_179) | ~r1_tarski(k1_tops_1(A_177, B_178), B_179) | ~v4_pre_topc(B_179, A_177) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_177))) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_20, c_1050])).
% 4.55/1.80  tff(c_1250, plain, (![A_180, B_181]: (k2_pre_topc(A_180, k1_tops_1(A_180, B_181))=B_181 | ~v4_tops_1(B_181, A_180) | ~r1_tarski(k1_tops_1(A_180, B_181), B_181) | ~v4_pre_topc(B_181, A_180) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(resolution, [status(thm)], [c_1236, c_1035])).
% 4.55/1.80  tff(c_1254, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_962, c_1250])).
% 4.55/1.80  tff(c_1260, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_940, c_942, c_1254])).
% 4.55/1.80  tff(c_990, plain, (![A_142, B_143]: (k2_pre_topc(A_142, k2_pre_topc(A_142, B_143))=k2_pre_topc(A_142, B_143) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.80  tff(c_1097, plain, (![A_161, B_162]: (k2_pre_topc(A_161, k2_pre_topc(A_161, k1_tops_1(A_161, B_162)))=k2_pre_topc(A_161, k1_tops_1(A_161, B_162)) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_20, c_990])).
% 4.55/1.80  tff(c_1103, plain, (k2_pre_topc('#skF_2', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1097])).
% 4.55/1.80  tff(c_1110, plain, (k2_pre_topc('#skF_2', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1103])).
% 4.55/1.80  tff(c_14, plain, (![A_5, B_7]: (r1_tarski(k1_tops_1(A_5, k2_pre_topc(A_5, B_7)), B_7) | ~v4_tops_1(B_7, A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/1.80  tff(c_1146, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))) | ~v4_tops_1(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1110, c_14])).
% 4.55/1.80  tff(c_1152, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))) | ~v4_tops_1(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1146])).
% 4.55/1.80  tff(c_1215, plain, (~m1_subset_1(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1152])).
% 4.55/1.80  tff(c_1264, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_1215])).
% 4.55/1.80  tff(c_1268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1264])).
% 4.55/1.80  tff(c_1270, plain, (m1_subset_1(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1152])).
% 4.55/1.80  tff(c_1056, plain, (![B_158]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), B_158) | ~r1_tarski('#skF_4', B_158) | ~v4_pre_topc(B_158, '#skF_2') | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_1050])).
% 4.55/1.80  tff(c_1063, plain, (![B_158]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), B_158) | ~r1_tarski('#skF_4', B_158) | ~v4_pre_topc(B_158, '#skF_2') | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1056])).
% 4.55/1.80  tff(c_1294, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))) | ~v4_pre_topc(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_1270, c_1063])).
% 4.55/1.80  tff(c_1313, plain, (~v4_pre_topc(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1294])).
% 4.55/1.80  tff(c_1405, plain, (~v4_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1398, c_1313])).
% 4.55/1.80  tff(c_1411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_940, c_1405])).
% 4.55/1.80  tff(c_1412, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))) | r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_1294])).
% 4.55/1.80  tff(c_1415, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1412])).
% 4.55/1.80  tff(c_1418, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_1415])).
% 4.55/1.80  tff(c_1422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_942, c_1418])).
% 4.55/1.80  tff(c_1424, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_1412])).
% 4.55/1.80  tff(c_1428, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4')), inference(resolution, [status(thm)], [c_1424, c_2])).
% 4.55/1.80  tff(c_1432, plain, (~r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_1428])).
% 4.55/1.80  tff(c_1436, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1433, c_1432])).
% 4.55/1.80  tff(c_1450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_940, c_962, c_1436])).
% 4.55/1.80  tff(c_1451, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_1428])).
% 4.55/1.80  tff(c_1484, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1451, c_16])).
% 4.55/1.80  tff(c_1501, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1484])).
% 4.55/1.80  tff(c_1503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_1501])).
% 4.55/1.80  tff(c_1504, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.55/1.80  tff(c_1578, plain, (![A_208, B_209]: (k2_pre_topc(A_208, k1_tops_1(A_208, B_209))=B_209 | ~v5_tops_1(B_209, A_208) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.55/1.80  tff(c_1582, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1578])).
% 4.55/1.80  tff(c_1588, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1504, c_1582])).
% 4.55/1.80  tff(c_1541, plain, (![A_204, B_205]: (v4_pre_topc(k2_pre_topc(A_204, B_205), A_204) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.80  tff(c_1635, plain, (![A_214, B_215]: (v4_pre_topc(k2_pre_topc(A_214, k1_tops_1(A_214, B_215)), A_214) | ~v2_pre_topc(A_214) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(resolution, [status(thm)], [c_20, c_1541])).
% 4.55/1.80  tff(c_1641, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1588, c_1635])).
% 4.55/1.80  tff(c_1645, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_36, c_1641])).
% 4.55/1.80  tff(c_1647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1515, c_1645])).
% 4.55/1.80  tff(c_1649, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.55/1.80  tff(c_1505, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.55/1.80  tff(c_38, plain, (~v5_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.55/1.80  tff(c_1652, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1505, c_38])).
% 4.55/1.80  tff(c_1655, plain, (![A_216, B_217]: (r1_tarski(k1_tops_1(A_216, B_217), B_217) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.55/1.80  tff(c_1657, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1655])).
% 4.55/1.80  tff(c_1662, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1657])).
% 4.55/1.80  tff(c_1707, plain, (![A_224, B_225]: (k2_pre_topc(A_224, k1_tops_1(A_224, B_225))=B_225 | ~v5_tops_1(B_225, A_224) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.55/1.80  tff(c_1711, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1707])).
% 4.55/1.80  tff(c_1717, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1504, c_1711])).
% 4.55/1.80  tff(c_1693, plain, (![A_222, B_223]: (k2_pre_topc(A_222, k2_pre_topc(A_222, B_223))=k2_pre_topc(A_222, B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.80  tff(c_1848, plain, (![A_241, B_242]: (k2_pre_topc(A_241, k2_pre_topc(A_241, k1_tops_1(A_241, B_242)))=k2_pre_topc(A_241, k1_tops_1(A_241, B_242)) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_20, c_1693])).
% 4.55/1.80  tff(c_1852, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1848])).
% 4.55/1.80  tff(c_1858, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1717, c_1717, c_1852])).
% 4.55/1.80  tff(c_1801, plain, (![A_236, C_237, B_238]: (r1_tarski(k2_pre_topc(A_236, C_237), B_238) | ~r1_tarski(C_237, B_238) | ~v4_pre_topc(B_238, A_236) | ~m1_subset_1(C_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.80  tff(c_1805, plain, (![B_238]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), B_238) | ~r1_tarski('#skF_3', B_238) | ~v4_pre_topc(B_238, '#skF_1') | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1801])).
% 4.55/1.80  tff(c_1815, plain, (![B_239]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), B_239) | ~r1_tarski('#skF_3', B_239) | ~v4_pre_topc(B_239, '#skF_1') | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1805])).
% 4.55/1.80  tff(c_1822, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_1815])).
% 4.55/1.80  tff(c_1828, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_6, c_1822])).
% 4.55/1.80  tff(c_1831, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1828, c_2])).
% 4.55/1.80  tff(c_1832, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1831])).
% 4.55/1.80  tff(c_1862, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1858, c_1832])).
% 4.55/1.80  tff(c_1869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1862])).
% 4.55/1.80  tff(c_1870, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1831])).
% 4.55/1.80  tff(c_1906, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1870, c_10])).
% 4.55/1.80  tff(c_1913, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1662, c_6, c_1717, c_1906])).
% 4.55/1.80  tff(c_1915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1652, c_1913])).
% 4.55/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.80  
% 4.55/1.80  Inference rules
% 4.55/1.80  ----------------------
% 4.55/1.80  #Ref     : 0
% 4.55/1.80  #Sup     : 382
% 4.55/1.80  #Fact    : 0
% 4.55/1.80  #Define  : 0
% 4.55/1.80  #Split   : 52
% 4.55/1.80  #Chain   : 0
% 4.55/1.80  #Close   : 0
% 4.55/1.80  
% 4.55/1.80  Ordering : KBO
% 4.55/1.80  
% 4.55/1.80  Simplification rules
% 4.55/1.80  ----------------------
% 4.55/1.80  #Subsume      : 43
% 4.55/1.80  #Demod        : 498
% 4.55/1.80  #Tautology    : 135
% 4.55/1.80  #SimpNegUnit  : 9
% 4.55/1.80  #BackRed      : 29
% 4.55/1.80  
% 4.55/1.80  #Partial instantiations: 0
% 4.55/1.80  #Strategies tried      : 1
% 4.55/1.80  
% 4.55/1.80  Timing (in seconds)
% 4.55/1.80  ----------------------
% 4.65/1.80  Preprocessing        : 0.31
% 4.65/1.80  Parsing              : 0.18
% 4.65/1.80  CNF conversion       : 0.02
% 4.65/1.80  Main loop            : 0.64
% 4.65/1.80  Inferencing          : 0.22
% 4.65/1.80  Reduction            : 0.21
% 4.65/1.80  Demodulation         : 0.15
% 4.65/1.81  BG Simplification    : 0.03
% 4.65/1.81  Subsumption          : 0.13
% 4.65/1.81  Abstraction          : 0.03
% 4.65/1.81  MUC search           : 0.00
% 4.65/1.81  Cooper               : 0.00
% 4.65/1.81  Total                : 1.05
% 4.65/1.81  Index Insertion      : 0.00
% 4.65/1.81  Index Deletion       : 0.00
% 4.65/1.81  Index Matching       : 0.00
% 4.65/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
