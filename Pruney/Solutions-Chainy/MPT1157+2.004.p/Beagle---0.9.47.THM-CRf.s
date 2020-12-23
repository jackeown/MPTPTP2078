%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:41 EST 2020

% Result     : Theorem 29.96s
% Output     : CNFRefutation 30.14s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 563 expanded)
%              Number of leaves         :   39 ( 210 expanded)
%              Depth                    :   19
%              Number of atoms          :  360 (2054 expanded)
%              Number of equality atoms :   35 ( 180 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_orders_2(A,B,C)
                <=> r2_hidden(C,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_159,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ ( ? [D] :
                        ( v6_orders_2(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(B,D)
                        & r2_hidden(C,D) )
                    & ~ r1_orders_2(A,B,C)
                    & ~ r1_orders_2(A,C,B) )
                & ~ ( ( r1_orders_2(A,B,C)
                      | r1_orders_2(A,C,B) )
                    & ! [D] :
                        ( ( v6_orders_2(D,A)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( r2_hidden(B,D)
                            & r2_hidden(C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_74,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_72,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_70,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_68,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_64,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_102867,plain,(
    ! [A_42176,B_42177] :
      ( k6_domain_1(A_42176,B_42177) = k1_tarski(B_42177)
      | ~ m1_subset_1(B_42177,A_42176)
      | v1_xboole_0(A_42176) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_102874,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_102867])).

tff(c_102876,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_102874])).

tff(c_102890,plain,(
    ! [A_42183,B_42184] :
      ( r1_orders_2(A_42183,B_42184,B_42184)
      | ~ m1_subset_1(B_42184,u1_struct_0(A_42183))
      | ~ l1_orders_2(A_42183)
      | ~ v3_orders_2(A_42183)
      | v2_struct_0(A_42183) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_102894,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_102890])).

tff(c_102901,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_102894])).

tff(c_102902,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_102901])).

tff(c_48,plain,(
    ! [A_37,C_55,B_49] :
      ( ~ r1_orders_2(A_37,C_55,B_49)
      | r2_hidden(C_55,'#skF_5'(A_37,B_49,C_55))
      | ~ m1_subset_1(C_55,u1_struct_0(A_37))
      | ~ m1_subset_1(B_49,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | ~ v3_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_106101,plain,(
    ! [A_46798,C_46799,B_46800] :
      ( ~ r1_orders_2(A_46798,C_46799,B_46800)
      | m1_subset_1('#skF_5'(A_46798,B_46800,C_46799),k1_zfmisc_1(u1_struct_0(A_46798)))
      | ~ m1_subset_1(C_46799,u1_struct_0(A_46798))
      | ~ m1_subset_1(B_46800,u1_struct_0(A_46798))
      | ~ l1_orders_2(A_46798)
      | ~ v3_orders_2(A_46798) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_24,plain,(
    ! [C_13,B_12,A_11] :
      ( ~ v1_xboole_0(C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(C_13))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_161086,plain,(
    ! [A_63481,A_63482,B_63483,C_63484] :
      ( ~ v1_xboole_0(u1_struct_0(A_63481))
      | ~ r2_hidden(A_63482,'#skF_5'(A_63481,B_63483,C_63484))
      | ~ r1_orders_2(A_63481,C_63484,B_63483)
      | ~ m1_subset_1(C_63484,u1_struct_0(A_63481))
      | ~ m1_subset_1(B_63483,u1_struct_0(A_63481))
      | ~ l1_orders_2(A_63481)
      | ~ v3_orders_2(A_63481) ) ),
    inference(resolution,[status(thm)],[c_106101,c_24])).

tff(c_161134,plain,(
    ! [A_63728,C_63729,B_63730] :
      ( ~ v1_xboole_0(u1_struct_0(A_63728))
      | ~ r1_orders_2(A_63728,C_63729,B_63730)
      | ~ m1_subset_1(C_63729,u1_struct_0(A_63728))
      | ~ m1_subset_1(B_63730,u1_struct_0(A_63728))
      | ~ l1_orders_2(A_63728)
      | ~ v3_orders_2(A_63728) ) ),
    inference(resolution,[status(thm)],[c_48,c_161086])).

tff(c_161136,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_102902,c_161134])).

tff(c_161142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_102876,c_161136])).

tff(c_161144,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_102874])).

tff(c_102875,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_102867])).

tff(c_161149,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_161144,c_102875])).

tff(c_161156,plain,(
    ! [A_63977,B_63978] :
      ( m1_subset_1(k6_domain_1(A_63977,B_63978),k1_zfmisc_1(A_63977))
      | ~ m1_subset_1(B_63978,A_63977)
      | v1_xboole_0(A_63977) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_161166,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_161149,c_161156])).

tff(c_161174,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_161166])).

tff(c_161175,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_161144,c_161174])).

tff(c_162688,plain,(
    ! [A_67819,B_67820] :
      ( k1_orders_2(A_67819,B_67820) = a_2_0_orders_2(A_67819,B_67820)
      | ~ m1_subset_1(B_67820,k1_zfmisc_1(u1_struct_0(A_67819)))
      | ~ l1_orders_2(A_67819)
      | ~ v5_orders_2(A_67819)
      | ~ v4_orders_2(A_67819)
      | ~ v3_orders_2(A_67819)
      | v2_struct_0(A_67819) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_162700,plain,
    ( k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_161175,c_162688])).

tff(c_162711,plain,
    ( k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_162700])).

tff(c_162712,plain,(
    k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_162711])).

tff(c_127,plain,(
    ! [A_80,B_81] :
      ( k6_domain_1(A_80,B_81) = k1_tarski(B_81)
      | ~ m1_subset_1(B_81,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_134,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_127])).

tff(c_136,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_152,plain,(
    ! [A_87,B_88] :
      ( r1_orders_2(A_87,B_88,B_88)
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_156,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_152])).

tff(c_163,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_156])).

tff(c_164,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_163])).

tff(c_50,plain,(
    ! [A_37,B_49,C_55] :
      ( ~ r1_orders_2(A_37,B_49,C_55)
      | r2_hidden(C_55,'#skF_5'(A_37,B_49,C_55))
      | ~ m1_subset_1(C_55,u1_struct_0(A_37))
      | ~ m1_subset_1(B_49,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | ~ v3_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4635,plain,(
    ! [A_5991,B_5992,C_5993] :
      ( ~ r1_orders_2(A_5991,B_5992,C_5993)
      | m1_subset_1('#skF_5'(A_5991,B_5992,C_5993),k1_zfmisc_1(u1_struct_0(A_5991)))
      | ~ m1_subset_1(C_5993,u1_struct_0(A_5991))
      | ~ m1_subset_1(B_5992,u1_struct_0(A_5991))
      | ~ l1_orders_2(A_5991)
      | ~ v3_orders_2(A_5991) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_84830,plain,(
    ! [A_26895,A_26896,B_26897,C_26898] :
      ( ~ v1_xboole_0(u1_struct_0(A_26895))
      | ~ r2_hidden(A_26896,'#skF_5'(A_26895,B_26897,C_26898))
      | ~ r1_orders_2(A_26895,B_26897,C_26898)
      | ~ m1_subset_1(C_26898,u1_struct_0(A_26895))
      | ~ m1_subset_1(B_26897,u1_struct_0(A_26895))
      | ~ l1_orders_2(A_26895)
      | ~ v3_orders_2(A_26895) ) ),
    inference(resolution,[status(thm)],[c_4635,c_24])).

tff(c_84878,plain,(
    ! [A_27142,B_27143,C_27144] :
      ( ~ v1_xboole_0(u1_struct_0(A_27142))
      | ~ r1_orders_2(A_27142,B_27143,C_27144)
      | ~ m1_subset_1(C_27144,u1_struct_0(A_27142))
      | ~ m1_subset_1(B_27143,u1_struct_0(A_27142))
      | ~ l1_orders_2(A_27142)
      | ~ v3_orders_2(A_27142) ) ),
    inference(resolution,[status(thm)],[c_50,c_84830])).

tff(c_84880,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_164,c_84878])).

tff(c_84886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_136,c_84880])).

tff(c_84888,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_135,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_127])).

tff(c_84927,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_84888,c_135])).

tff(c_84,plain,
    ( r2_orders_2('#skF_6','#skF_7','#skF_8')
    | r2_hidden('#skF_8',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_98,plain,(
    r2_hidden('#skF_8',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_84928,plain,(
    r2_hidden('#skF_8',k1_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84927,c_98])).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_8',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7')))
    | ~ r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_84939,plain,
    ( ~ r2_hidden('#skF_8',k1_orders_2('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84927,c_78])).

tff(c_84940,plain,(
    ~ r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84939])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    ! [D_64,B_65] : r2_hidden(D_64,k2_tarski(D_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k6_domain_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84932,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84927,c_28])).

tff(c_84936,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_84932])).

tff(c_84937,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84888,c_84936])).

tff(c_86975,plain,(
    ! [A_31890,B_31891] :
      ( k1_orders_2(A_31890,B_31891) = a_2_0_orders_2(A_31890,B_31891)
      | ~ m1_subset_1(B_31891,k1_zfmisc_1(u1_struct_0(A_31890)))
      | ~ l1_orders_2(A_31890)
      | ~ v5_orders_2(A_31890)
      | ~ v4_orders_2(A_31890)
      | ~ v3_orders_2(A_31890)
      | v2_struct_0(A_31890) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86984,plain,
    ( k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_84937,c_86975])).

tff(c_86994,plain,
    ( k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_86984])).

tff(c_86995,plain,(
    k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_86994])).

tff(c_87002,plain,(
    r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86995,c_84928])).

tff(c_93430,plain,(
    ! [A_37229,B_37230,C_37231] :
      ( '#skF_3'(A_37229,B_37230,C_37231) = A_37229
      | ~ r2_hidden(A_37229,a_2_0_orders_2(B_37230,C_37231))
      | ~ m1_subset_1(C_37231,k1_zfmisc_1(u1_struct_0(B_37230)))
      | ~ l1_orders_2(B_37230)
      | ~ v5_orders_2(B_37230)
      | ~ v4_orders_2(B_37230)
      | ~ v3_orders_2(B_37230)
      | v2_struct_0(B_37230) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_93432,plain,
    ( '#skF_3'('#skF_8','#skF_6',k1_tarski('#skF_7')) = '#skF_8'
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_87002,c_93430])).

tff(c_93441,plain,
    ( '#skF_3'('#skF_8','#skF_6',k1_tarski('#skF_7')) = '#skF_8'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_84937,c_93432])).

tff(c_93442,plain,(
    '#skF_3'('#skF_8','#skF_6',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_93441])).

tff(c_100322,plain,(
    ! [B_41175,E_41176,A_41177,C_41178] :
      ( r2_orders_2(B_41175,E_41176,'#skF_3'(A_41177,B_41175,C_41178))
      | ~ r2_hidden(E_41176,C_41178)
      | ~ m1_subset_1(E_41176,u1_struct_0(B_41175))
      | ~ r2_hidden(A_41177,a_2_0_orders_2(B_41175,C_41178))
      | ~ m1_subset_1(C_41178,k1_zfmisc_1(u1_struct_0(B_41175)))
      | ~ l1_orders_2(B_41175)
      | ~ v5_orders_2(B_41175)
      | ~ v4_orders_2(B_41175)
      | ~ v3_orders_2(B_41175)
      | v2_struct_0(B_41175) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_100336,plain,(
    ! [E_41176,A_41177] :
      ( r2_orders_2('#skF_6',E_41176,'#skF_3'(A_41177,'#skF_6',k1_tarski('#skF_7')))
      | ~ r2_hidden(E_41176,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_41176,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_41177,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_84937,c_100322])).

tff(c_100350,plain,(
    ! [E_41176,A_41177] :
      ( r2_orders_2('#skF_6',E_41176,'#skF_3'(A_41177,'#skF_6',k1_tarski('#skF_7')))
      | ~ r2_hidden(E_41176,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_41176,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_41177,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_100336])).

tff(c_102756,plain,(
    ! [E_42000,A_42001] :
      ( r2_orders_2('#skF_6',E_42000,'#skF_3'(A_42001,'#skF_6',k1_tarski('#skF_7')))
      | ~ r2_hidden(E_42000,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_42000,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_42001,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_100350])).

tff(c_102762,plain,(
    ! [E_42000] :
      ( r2_orders_2('#skF_6',E_42000,'#skF_8')
      | ~ r2_hidden(E_42000,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_42000,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93442,c_102756])).

tff(c_102809,plain,(
    ! [E_42083] :
      ( r2_orders_2('#skF_6',E_42083,'#skF_8')
      | ~ r2_hidden(E_42083,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_42083,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87002,c_102762])).

tff(c_102824,plain,
    ( r2_orders_2('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_97,c_102809])).

tff(c_102829,plain,(
    r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_102824])).

tff(c_102831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84940,c_102829])).

tff(c_102832,plain,(
    ~ r2_hidden('#skF_8',k1_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_84939])).

tff(c_102835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84928,c_102832])).

tff(c_102837,plain,(
    ~ r2_hidden('#skF_8',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_161150,plain,(
    ~ r2_hidden('#skF_8',k1_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161149,c_102837])).

tff(c_162773,plain,(
    ~ r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162712,c_161150])).

tff(c_102836,plain,(
    r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_169066,plain,(
    ! [D_73743,B_73744,C_73745] :
      ( r2_hidden('#skF_4'(D_73743,B_73744,C_73745,D_73743),C_73745)
      | r2_hidden(D_73743,a_2_0_orders_2(B_73744,C_73745))
      | ~ m1_subset_1(D_73743,u1_struct_0(B_73744))
      | ~ m1_subset_1(C_73745,k1_zfmisc_1(u1_struct_0(B_73744)))
      | ~ l1_orders_2(B_73744)
      | ~ v5_orders_2(B_73744)
      | ~ v4_orders_2(B_73744)
      | ~ v3_orders_2(B_73744)
      | v2_struct_0(B_73744) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_169080,plain,(
    ! [D_73743] :
      ( r2_hidden('#skF_4'(D_73743,'#skF_6',k1_tarski('#skF_7'),D_73743),k1_tarski('#skF_7'))
      | r2_hidden(D_73743,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_73743,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_161175,c_169066])).

tff(c_169092,plain,(
    ! [D_73743] :
      ( r2_hidden('#skF_4'(D_73743,'#skF_6',k1_tarski('#skF_7'),D_73743),k1_tarski('#skF_7'))
      | r2_hidden(D_73743,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_73743,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_169080])).

tff(c_171288,plain,(
    ! [D_74895] :
      ( r2_hidden('#skF_4'(D_74895,'#skF_6',k1_tarski('#skF_7'),D_74895),k1_tarski('#skF_7'))
      | r2_hidden(D_74895,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_74895,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_169092])).

tff(c_102847,plain,(
    ! [D_42171,B_42172,A_42173] :
      ( D_42171 = B_42172
      | D_42171 = A_42173
      | ~ r2_hidden(D_42171,k2_tarski(A_42173,B_42172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102856,plain,(
    ! [D_42171,A_7] :
      ( D_42171 = A_7
      | D_42171 = A_7
      | ~ r2_hidden(D_42171,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_102847])).

tff(c_174889,plain,(
    ! [D_77032] :
      ( '#skF_4'(D_77032,'#skF_6',k1_tarski('#skF_7'),D_77032) = '#skF_7'
      | r2_hidden(D_77032,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_77032,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_171288,c_102856])).

tff(c_174917,plain,
    ( '#skF_4'('#skF_8','#skF_6',k1_tarski('#skF_7'),'#skF_8') = '#skF_7'
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_174889,c_162773])).

tff(c_175022,plain,(
    '#skF_4'('#skF_8','#skF_6',k1_tarski('#skF_7'),'#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_174917])).

tff(c_30,plain,(
    ! [B_20,D_30,C_21] :
      ( ~ r2_orders_2(B_20,'#skF_4'(D_30,B_20,C_21,D_30),D_30)
      | r2_hidden(D_30,a_2_0_orders_2(B_20,C_21))
      | ~ m1_subset_1(D_30,u1_struct_0(B_20))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(B_20)))
      | ~ l1_orders_2(B_20)
      | ~ v5_orders_2(B_20)
      | ~ v4_orders_2(B_20)
      | ~ v3_orders_2(B_20)
      | v2_struct_0(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_175033,plain,
    ( ~ r2_orders_2('#skF_6','#skF_7','#skF_8')
    | r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_175022,c_30])).

tff(c_175081,plain,
    ( r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_161175,c_64,c_102836,c_175033])).

tff(c_175083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_162773,c_175081])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.96/17.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.96/17.87  
% 29.96/17.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.96/17.88  %$ r2_orders_2 > r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 29.96/17.88  
% 29.96/17.88  %Foreground sorts:
% 29.96/17.88  
% 29.96/17.88  
% 29.96/17.88  %Background operators:
% 29.96/17.88  
% 29.96/17.88  
% 29.96/17.88  %Foreground operators:
% 29.96/17.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 29.96/17.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 29.96/17.88  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 29.96/17.88  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 29.96/17.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.96/17.88  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 29.96/17.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.96/17.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 29.96/17.88  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 29.96/17.88  tff('#skF_7', type, '#skF_7': $i).
% 29.96/17.88  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 29.96/17.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 29.96/17.88  tff('#skF_6', type, '#skF_6': $i).
% 29.96/17.88  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 29.96/17.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 29.96/17.88  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 29.96/17.88  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 29.96/17.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.96/17.88  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 29.96/17.88  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 29.96/17.88  tff('#skF_8', type, '#skF_8': $i).
% 29.96/17.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.96/17.88  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 29.96/17.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.96/17.88  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 29.96/17.88  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 29.96/17.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 29.96/17.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 29.96/17.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.96/17.88  
% 30.14/17.90  tff(f_181, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(C, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_orders_2)).
% 30.14/17.90  tff(f_106, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 30.14/17.90  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 30.14/17.90  tff(f_159, axiom, (![A]: ((v3_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~(((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) & ~r1_orders_2(A, B, C)) & ~r1_orders_2(A, C, B)) & ~((r1_orders_2(A, B, C) | r1_orders_2(A, C, B)) & (![D]: ((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~(r2_hidden(B, D) & r2_hidden(C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_orders_2)).
% 30.14/17.90  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 30.14/17.90  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 30.14/17.90  tff(f_65, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 30.14/17.90  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 30.14/17.90  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 30.14/17.90  tff(f_99, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 30.14/17.90  tff(c_76, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_74, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_72, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_70, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_68, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_66, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_64, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_102867, plain, (![A_42176, B_42177]: (k6_domain_1(A_42176, B_42177)=k1_tarski(B_42177) | ~m1_subset_1(B_42177, A_42176) | v1_xboole_0(A_42176))), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.14/17.90  tff(c_102874, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_102867])).
% 30.14/17.90  tff(c_102876, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_102874])).
% 30.14/17.90  tff(c_102890, plain, (![A_42183, B_42184]: (r1_orders_2(A_42183, B_42184, B_42184) | ~m1_subset_1(B_42184, u1_struct_0(A_42183)) | ~l1_orders_2(A_42183) | ~v3_orders_2(A_42183) | v2_struct_0(A_42183))), inference(cnfTransformation, [status(thm)], [f_118])).
% 30.14/17.90  tff(c_102894, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_102890])).
% 30.14/17.90  tff(c_102901, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_102894])).
% 30.14/17.90  tff(c_102902, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_76, c_102901])).
% 30.14/17.90  tff(c_48, plain, (![A_37, C_55, B_49]: (~r1_orders_2(A_37, C_55, B_49) | r2_hidden(C_55, '#skF_5'(A_37, B_49, C_55)) | ~m1_subset_1(C_55, u1_struct_0(A_37)) | ~m1_subset_1(B_49, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | ~v3_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_159])).
% 30.14/17.90  tff(c_106101, plain, (![A_46798, C_46799, B_46800]: (~r1_orders_2(A_46798, C_46799, B_46800) | m1_subset_1('#skF_5'(A_46798, B_46800, C_46799), k1_zfmisc_1(u1_struct_0(A_46798))) | ~m1_subset_1(C_46799, u1_struct_0(A_46798)) | ~m1_subset_1(B_46800, u1_struct_0(A_46798)) | ~l1_orders_2(A_46798) | ~v3_orders_2(A_46798))), inference(cnfTransformation, [status(thm)], [f_159])).
% 30.14/17.90  tff(c_24, plain, (![C_13, B_12, A_11]: (~v1_xboole_0(C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(C_13)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 30.14/17.90  tff(c_161086, plain, (![A_63481, A_63482, B_63483, C_63484]: (~v1_xboole_0(u1_struct_0(A_63481)) | ~r2_hidden(A_63482, '#skF_5'(A_63481, B_63483, C_63484)) | ~r1_orders_2(A_63481, C_63484, B_63483) | ~m1_subset_1(C_63484, u1_struct_0(A_63481)) | ~m1_subset_1(B_63483, u1_struct_0(A_63481)) | ~l1_orders_2(A_63481) | ~v3_orders_2(A_63481))), inference(resolution, [status(thm)], [c_106101, c_24])).
% 30.14/17.90  tff(c_161134, plain, (![A_63728, C_63729, B_63730]: (~v1_xboole_0(u1_struct_0(A_63728)) | ~r1_orders_2(A_63728, C_63729, B_63730) | ~m1_subset_1(C_63729, u1_struct_0(A_63728)) | ~m1_subset_1(B_63730, u1_struct_0(A_63728)) | ~l1_orders_2(A_63728) | ~v3_orders_2(A_63728))), inference(resolution, [status(thm)], [c_48, c_161086])).
% 30.14/17.90  tff(c_161136, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_102902, c_161134])).
% 30.14/17.90  tff(c_161142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_102876, c_161136])).
% 30.14/17.90  tff(c_161144, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_102874])).
% 30.14/17.90  tff(c_102875, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_102867])).
% 30.14/17.90  tff(c_161149, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_161144, c_102875])).
% 30.14/17.90  tff(c_161156, plain, (![A_63977, B_63978]: (m1_subset_1(k6_domain_1(A_63977, B_63978), k1_zfmisc_1(A_63977)) | ~m1_subset_1(B_63978, A_63977) | v1_xboole_0(A_63977))), inference(cnfTransformation, [status(thm)], [f_72])).
% 30.14/17.90  tff(c_161166, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_161149, c_161156])).
% 30.14/17.90  tff(c_161174, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_161166])).
% 30.14/17.90  tff(c_161175, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_161144, c_161174])).
% 30.14/17.90  tff(c_162688, plain, (![A_67819, B_67820]: (k1_orders_2(A_67819, B_67820)=a_2_0_orders_2(A_67819, B_67820) | ~m1_subset_1(B_67820, k1_zfmisc_1(u1_struct_0(A_67819))) | ~l1_orders_2(A_67819) | ~v5_orders_2(A_67819) | ~v4_orders_2(A_67819) | ~v3_orders_2(A_67819) | v2_struct_0(A_67819))), inference(cnfTransformation, [status(thm)], [f_65])).
% 30.14/17.90  tff(c_162700, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_161175, c_162688])).
% 30.14/17.90  tff(c_162711, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_162700])).
% 30.14/17.90  tff(c_162712, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_76, c_162711])).
% 30.14/17.90  tff(c_127, plain, (![A_80, B_81]: (k6_domain_1(A_80, B_81)=k1_tarski(B_81) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.14/17.90  tff(c_134, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_127])).
% 30.14/17.90  tff(c_136, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_134])).
% 30.14/17.90  tff(c_152, plain, (![A_87, B_88]: (r1_orders_2(A_87, B_88, B_88) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_118])).
% 30.14/17.90  tff(c_156, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_152])).
% 30.14/17.90  tff(c_163, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_156])).
% 30.14/17.90  tff(c_164, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_76, c_163])).
% 30.14/17.90  tff(c_50, plain, (![A_37, B_49, C_55]: (~r1_orders_2(A_37, B_49, C_55) | r2_hidden(C_55, '#skF_5'(A_37, B_49, C_55)) | ~m1_subset_1(C_55, u1_struct_0(A_37)) | ~m1_subset_1(B_49, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | ~v3_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_159])).
% 30.14/17.90  tff(c_4635, plain, (![A_5991, B_5992, C_5993]: (~r1_orders_2(A_5991, B_5992, C_5993) | m1_subset_1('#skF_5'(A_5991, B_5992, C_5993), k1_zfmisc_1(u1_struct_0(A_5991))) | ~m1_subset_1(C_5993, u1_struct_0(A_5991)) | ~m1_subset_1(B_5992, u1_struct_0(A_5991)) | ~l1_orders_2(A_5991) | ~v3_orders_2(A_5991))), inference(cnfTransformation, [status(thm)], [f_159])).
% 30.14/17.90  tff(c_84830, plain, (![A_26895, A_26896, B_26897, C_26898]: (~v1_xboole_0(u1_struct_0(A_26895)) | ~r2_hidden(A_26896, '#skF_5'(A_26895, B_26897, C_26898)) | ~r1_orders_2(A_26895, B_26897, C_26898) | ~m1_subset_1(C_26898, u1_struct_0(A_26895)) | ~m1_subset_1(B_26897, u1_struct_0(A_26895)) | ~l1_orders_2(A_26895) | ~v3_orders_2(A_26895))), inference(resolution, [status(thm)], [c_4635, c_24])).
% 30.14/17.90  tff(c_84878, plain, (![A_27142, B_27143, C_27144]: (~v1_xboole_0(u1_struct_0(A_27142)) | ~r1_orders_2(A_27142, B_27143, C_27144) | ~m1_subset_1(C_27144, u1_struct_0(A_27142)) | ~m1_subset_1(B_27143, u1_struct_0(A_27142)) | ~l1_orders_2(A_27142) | ~v3_orders_2(A_27142))), inference(resolution, [status(thm)], [c_50, c_84830])).
% 30.14/17.90  tff(c_84880, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_164, c_84878])).
% 30.14/17.90  tff(c_84886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_136, c_84880])).
% 30.14/17.90  tff(c_84888, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_134])).
% 30.14/17.90  tff(c_135, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_127])).
% 30.14/17.90  tff(c_84927, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_84888, c_135])).
% 30.14/17.90  tff(c_84, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8') | r2_hidden('#skF_8', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_98, plain, (r2_hidden('#skF_8', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')))), inference(splitLeft, [status(thm)], [c_84])).
% 30.14/17.90  tff(c_84928, plain, (r2_hidden('#skF_8', k1_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_84927, c_98])).
% 30.14/17.90  tff(c_78, plain, (~r2_hidden('#skF_8', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'))) | ~r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_181])).
% 30.14/17.90  tff(c_84939, plain, (~r2_hidden('#skF_8', k1_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84927, c_78])).
% 30.14/17.90  tff(c_84940, plain, (~r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_84939])).
% 30.14/17.90  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 30.14/17.90  tff(c_94, plain, (![D_64, B_65]: (r2_hidden(D_64, k2_tarski(D_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 30.14/17.90  tff(c_97, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 30.14/17.90  tff(c_28, plain, (![A_17, B_18]: (m1_subset_1(k6_domain_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 30.14/17.90  tff(c_84932, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_84927, c_28])).
% 30.14/17.90  tff(c_84936, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_84932])).
% 30.14/17.90  tff(c_84937, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_84888, c_84936])).
% 30.14/17.90  tff(c_86975, plain, (![A_31890, B_31891]: (k1_orders_2(A_31890, B_31891)=a_2_0_orders_2(A_31890, B_31891) | ~m1_subset_1(B_31891, k1_zfmisc_1(u1_struct_0(A_31890))) | ~l1_orders_2(A_31890) | ~v5_orders_2(A_31890) | ~v4_orders_2(A_31890) | ~v3_orders_2(A_31890) | v2_struct_0(A_31890))), inference(cnfTransformation, [status(thm)], [f_65])).
% 30.14/17.90  tff(c_86984, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_84937, c_86975])).
% 30.14/17.90  tff(c_86994, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_86984])).
% 30.14/17.90  tff(c_86995, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_76, c_86994])).
% 30.14/17.90  tff(c_87002, plain, (r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_86995, c_84928])).
% 30.14/17.90  tff(c_93430, plain, (![A_37229, B_37230, C_37231]: ('#skF_3'(A_37229, B_37230, C_37231)=A_37229 | ~r2_hidden(A_37229, a_2_0_orders_2(B_37230, C_37231)) | ~m1_subset_1(C_37231, k1_zfmisc_1(u1_struct_0(B_37230))) | ~l1_orders_2(B_37230) | ~v5_orders_2(B_37230) | ~v4_orders_2(B_37230) | ~v3_orders_2(B_37230) | v2_struct_0(B_37230))), inference(cnfTransformation, [status(thm)], [f_99])).
% 30.14/17.90  tff(c_93432, plain, ('#skF_3'('#skF_8', '#skF_6', k1_tarski('#skF_7'))='#skF_8' | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_87002, c_93430])).
% 30.14/17.90  tff(c_93441, plain, ('#skF_3'('#skF_8', '#skF_6', k1_tarski('#skF_7'))='#skF_8' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_84937, c_93432])).
% 30.14/17.90  tff(c_93442, plain, ('#skF_3'('#skF_8', '#skF_6', k1_tarski('#skF_7'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_76, c_93441])).
% 30.14/17.90  tff(c_100322, plain, (![B_41175, E_41176, A_41177, C_41178]: (r2_orders_2(B_41175, E_41176, '#skF_3'(A_41177, B_41175, C_41178)) | ~r2_hidden(E_41176, C_41178) | ~m1_subset_1(E_41176, u1_struct_0(B_41175)) | ~r2_hidden(A_41177, a_2_0_orders_2(B_41175, C_41178)) | ~m1_subset_1(C_41178, k1_zfmisc_1(u1_struct_0(B_41175))) | ~l1_orders_2(B_41175) | ~v5_orders_2(B_41175) | ~v4_orders_2(B_41175) | ~v3_orders_2(B_41175) | v2_struct_0(B_41175))), inference(cnfTransformation, [status(thm)], [f_99])).
% 30.14/17.90  tff(c_100336, plain, (![E_41176, A_41177]: (r2_orders_2('#skF_6', E_41176, '#skF_3'(A_41177, '#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden(E_41176, k1_tarski('#skF_7')) | ~m1_subset_1(E_41176, u1_struct_0('#skF_6')) | ~r2_hidden(A_41177, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_84937, c_100322])).
% 30.14/17.90  tff(c_100350, plain, (![E_41176, A_41177]: (r2_orders_2('#skF_6', E_41176, '#skF_3'(A_41177, '#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden(E_41176, k1_tarski('#skF_7')) | ~m1_subset_1(E_41176, u1_struct_0('#skF_6')) | ~r2_hidden(A_41177, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_100336])).
% 30.14/17.90  tff(c_102756, plain, (![E_42000, A_42001]: (r2_orders_2('#skF_6', E_42000, '#skF_3'(A_42001, '#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden(E_42000, k1_tarski('#skF_7')) | ~m1_subset_1(E_42000, u1_struct_0('#skF_6')) | ~r2_hidden(A_42001, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_100350])).
% 30.14/17.90  tff(c_102762, plain, (![E_42000]: (r2_orders_2('#skF_6', E_42000, '#skF_8') | ~r2_hidden(E_42000, k1_tarski('#skF_7')) | ~m1_subset_1(E_42000, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_93442, c_102756])).
% 30.14/17.90  tff(c_102809, plain, (![E_42083]: (r2_orders_2('#skF_6', E_42083, '#skF_8') | ~r2_hidden(E_42083, k1_tarski('#skF_7')) | ~m1_subset_1(E_42083, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_87002, c_102762])).
% 30.14/17.90  tff(c_102824, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_97, c_102809])).
% 30.14/17.90  tff(c_102829, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_102824])).
% 30.14/17.90  tff(c_102831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84940, c_102829])).
% 30.14/17.90  tff(c_102832, plain, (~r2_hidden('#skF_8', k1_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(splitRight, [status(thm)], [c_84939])).
% 30.14/17.90  tff(c_102835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84928, c_102832])).
% 30.14/17.90  tff(c_102837, plain, (~r2_hidden('#skF_8', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')))), inference(splitRight, [status(thm)], [c_84])).
% 30.14/17.90  tff(c_161150, plain, (~r2_hidden('#skF_8', k1_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_161149, c_102837])).
% 30.14/17.90  tff(c_162773, plain, (~r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_162712, c_161150])).
% 30.14/17.90  tff(c_102836, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 30.14/17.90  tff(c_169066, plain, (![D_73743, B_73744, C_73745]: (r2_hidden('#skF_4'(D_73743, B_73744, C_73745, D_73743), C_73745) | r2_hidden(D_73743, a_2_0_orders_2(B_73744, C_73745)) | ~m1_subset_1(D_73743, u1_struct_0(B_73744)) | ~m1_subset_1(C_73745, k1_zfmisc_1(u1_struct_0(B_73744))) | ~l1_orders_2(B_73744) | ~v5_orders_2(B_73744) | ~v4_orders_2(B_73744) | ~v3_orders_2(B_73744) | v2_struct_0(B_73744))), inference(cnfTransformation, [status(thm)], [f_99])).
% 30.14/17.90  tff(c_169080, plain, (![D_73743]: (r2_hidden('#skF_4'(D_73743, '#skF_6', k1_tarski('#skF_7'), D_73743), k1_tarski('#skF_7')) | r2_hidden(D_73743, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(D_73743, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_161175, c_169066])).
% 30.14/17.90  tff(c_169092, plain, (![D_73743]: (r2_hidden('#skF_4'(D_73743, '#skF_6', k1_tarski('#skF_7'), D_73743), k1_tarski('#skF_7')) | r2_hidden(D_73743, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(D_73743, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_169080])).
% 30.14/17.90  tff(c_171288, plain, (![D_74895]: (r2_hidden('#skF_4'(D_74895, '#skF_6', k1_tarski('#skF_7'), D_74895), k1_tarski('#skF_7')) | r2_hidden(D_74895, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(D_74895, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_169092])).
% 30.14/17.90  tff(c_102847, plain, (![D_42171, B_42172, A_42173]: (D_42171=B_42172 | D_42171=A_42173 | ~r2_hidden(D_42171, k2_tarski(A_42173, B_42172)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 30.14/17.90  tff(c_102856, plain, (![D_42171, A_7]: (D_42171=A_7 | D_42171=A_7 | ~r2_hidden(D_42171, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_102847])).
% 30.14/17.90  tff(c_174889, plain, (![D_77032]: ('#skF_4'(D_77032, '#skF_6', k1_tarski('#skF_7'), D_77032)='#skF_7' | r2_hidden(D_77032, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(D_77032, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_171288, c_102856])).
% 30.14/17.90  tff(c_174917, plain, ('#skF_4'('#skF_8', '#skF_6', k1_tarski('#skF_7'), '#skF_8')='#skF_7' | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_174889, c_162773])).
% 30.14/17.90  tff(c_175022, plain, ('#skF_4'('#skF_8', '#skF_6', k1_tarski('#skF_7'), '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_174917])).
% 30.14/17.90  tff(c_30, plain, (![B_20, D_30, C_21]: (~r2_orders_2(B_20, '#skF_4'(D_30, B_20, C_21, D_30), D_30) | r2_hidden(D_30, a_2_0_orders_2(B_20, C_21)) | ~m1_subset_1(D_30, u1_struct_0(B_20)) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(B_20))) | ~l1_orders_2(B_20) | ~v5_orders_2(B_20) | ~v4_orders_2(B_20) | ~v3_orders_2(B_20) | v2_struct_0(B_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 30.14/17.90  tff(c_175033, plain, (~r2_orders_2('#skF_6', '#skF_7', '#skF_8') | r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_175022, c_30])).
% 30.14/17.90  tff(c_175081, plain, (r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_161175, c_64, c_102836, c_175033])).
% 30.14/17.90  tff(c_175083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_162773, c_175081])).
% 30.14/17.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.14/17.90  
% 30.14/17.90  Inference rules
% 30.14/17.90  ----------------------
% 30.14/17.90  #Ref     : 0
% 30.14/17.90  #Sup     : 23321
% 30.14/17.90  #Fact    : 210
% 30.14/17.90  #Define  : 0
% 30.14/17.90  #Split   : 57
% 30.14/17.90  #Chain   : 0
% 30.14/17.90  #Close   : 0
% 30.14/17.90  
% 30.14/17.90  Ordering : KBO
% 30.14/17.90  
% 30.14/17.90  Simplification rules
% 30.14/17.90  ----------------------
% 30.14/17.90  #Subsume      : 4037
% 30.14/17.90  #Demod        : 2010
% 30.14/17.90  #Tautology    : 2479
% 30.14/17.90  #SimpNegUnit  : 1073
% 30.14/17.90  #BackRed      : 5
% 30.14/17.90  
% 30.14/17.90  #Partial instantiations: 42390
% 30.14/17.90  #Strategies tried      : 1
% 30.14/17.90  
% 30.14/17.90  Timing (in seconds)
% 30.14/17.90  ----------------------
% 30.14/17.90  Preprocessing        : 0.43
% 30.14/17.90  Parsing              : 0.22
% 30.14/17.90  CNF conversion       : 0.03
% 30.14/17.90  Main loop            : 16.62
% 30.14/17.90  Inferencing          : 4.67
% 30.14/17.90  Reduction            : 2.63
% 30.14/17.90  Demodulation         : 1.88
% 30.14/17.90  BG Simplification    : 0.81
% 30.14/17.90  Subsumption          : 7.99
% 30.14/17.90  Abstraction          : 1.27
% 30.14/17.90  MUC search           : 0.00
% 30.14/17.90  Cooper               : 0.00
% 30.14/17.90  Total                : 17.09
% 30.14/17.90  Index Insertion      : 0.00
% 30.14/17.90  Index Deletion       : 0.00
% 30.14/17.90  Index Matching       : 0.00
% 30.14/17.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
