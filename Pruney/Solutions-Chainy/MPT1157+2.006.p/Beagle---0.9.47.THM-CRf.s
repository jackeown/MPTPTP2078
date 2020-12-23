%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:41 EST 2020

% Result     : Theorem 36.89s
% Output     : CNFRefutation 36.89s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 487 expanded)
%              Number of leaves         :   39 ( 194 expanded)
%              Depth                    :   19
%              Number of atoms          :  364 (1964 expanded)
%              Number of equality atoms :   34 ( 117 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

tff(f_182,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_160,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_86,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_74,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_72,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_70,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_68,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_181679,plain,(
    ! [A_60475,B_60476] :
      ( k6_domain_1(A_60475,B_60476) = k1_tarski(B_60476)
      | ~ m1_subset_1(B_60476,A_60475)
      | v1_xboole_0(A_60475) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_181687,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_181679])).

tff(c_181701,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_181687])).

tff(c_181688,plain,(
    ! [A_60477,B_60478] :
      ( r1_orders_2(A_60477,B_60478,B_60478)
      | ~ m1_subset_1(B_60478,u1_struct_0(A_60477))
      | ~ l1_orders_2(A_60477)
      | ~ v3_orders_2(A_60477)
      | v2_struct_0(A_60477) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_181692,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_181688])).

tff(c_181699,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_181692])).

tff(c_181700,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_181699])).

tff(c_48,plain,(
    ! [A_35,C_53,B_47] :
      ( ~ r1_orders_2(A_35,C_53,B_47)
      | r2_hidden(C_53,'#skF_5'(A_35,B_47,C_53))
      | ~ m1_subset_1(C_53,u1_struct_0(A_35))
      | ~ m1_subset_1(B_47,u1_struct_0(A_35))
      | ~ l1_orders_2(A_35)
      | ~ v3_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_185071,plain,(
    ! [A_65096,C_65097,B_65098] :
      ( ~ r1_orders_2(A_65096,C_65097,B_65098)
      | m1_subset_1('#skF_5'(A_65096,B_65098,C_65097),k1_zfmisc_1(u1_struct_0(A_65096)))
      | ~ m1_subset_1(C_65097,u1_struct_0(A_65096))
      | ~ m1_subset_1(B_65098,u1_struct_0(A_65096))
      | ~ l1_orders_2(A_65096)
      | ~ v3_orders_2(A_65096) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_22,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_239980,plain,(
    ! [A_81534,A_81535,B_81536,C_81537] :
      ( ~ v1_xboole_0(u1_struct_0(A_81534))
      | ~ r2_hidden(A_81535,'#skF_5'(A_81534,B_81536,C_81537))
      | ~ r1_orders_2(A_81534,C_81537,B_81536)
      | ~ m1_subset_1(C_81537,u1_struct_0(A_81534))
      | ~ m1_subset_1(B_81536,u1_struct_0(A_81534))
      | ~ l1_orders_2(A_81534)
      | ~ v3_orders_2(A_81534) ) ),
    inference(resolution,[status(thm)],[c_185071,c_22])).

tff(c_240028,plain,(
    ! [A_81781,C_81782,B_81783] :
      ( ~ v1_xboole_0(u1_struct_0(A_81781))
      | ~ r1_orders_2(A_81781,C_81782,B_81783)
      | ~ m1_subset_1(C_81782,u1_struct_0(A_81781))
      | ~ m1_subset_1(B_81783,u1_struct_0(A_81781))
      | ~ l1_orders_2(A_81781)
      | ~ v3_orders_2(A_81781) ) ),
    inference(resolution,[status(thm)],[c_48,c_239980])).

tff(c_240030,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_181700,c_240028])).

tff(c_240036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_181701,c_240030])).

tff(c_240037,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_181687])).

tff(c_240065,plain,(
    ! [A_82038,B_82039] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_82038),B_82039),k1_zfmisc_1(u1_struct_0(A_82038)))
      | ~ m1_subset_1(B_82039,u1_struct_0(A_82038))
      | ~ l1_orders_2(A_82038)
      | ~ v3_orders_2(A_82038)
      | v2_struct_0(A_82038) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_240073,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_240037,c_240065])).

tff(c_240080,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_240073])).

tff(c_240081,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_240080])).

tff(c_241538,plain,(
    ! [A_85780,B_85781] :
      ( k1_orders_2(A_85780,B_85781) = a_2_0_orders_2(A_85780,B_85781)
      | ~ m1_subset_1(B_85781,k1_zfmisc_1(u1_struct_0(A_85780)))
      | ~ l1_orders_2(A_85780)
      | ~ v5_orders_2(A_85780)
      | ~ v4_orders_2(A_85780)
      | ~ v3_orders_2(A_85780)
      | v2_struct_0(A_85780) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_241550,plain,
    ( k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_240081,c_241538])).

tff(c_241560,plain,
    ( k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_241550])).

tff(c_241561,plain,(
    k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_241560])).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_8',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7')))
    | ~ r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_98,plain,(
    ~ r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    ! [D_62,B_63] : r2_hidden(D_62,k2_tarski(D_62,B_63)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_64,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_126,plain,(
    ! [A_75,B_76] :
      ( k6_domain_1(A_75,B_76) = k1_tarski(B_76)
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_133,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_126])).

tff(c_135,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_138,plain,(
    ! [A_77,B_78] :
      ( r1_orders_2(A_77,B_78,B_78)
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_142,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_138])).

tff(c_149,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_142])).

tff(c_150,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_149])).

tff(c_50,plain,(
    ! [A_35,B_47,C_53] :
      ( ~ r1_orders_2(A_35,B_47,C_53)
      | r2_hidden(C_53,'#skF_5'(A_35,B_47,C_53))
      | ~ m1_subset_1(C_53,u1_struct_0(A_35))
      | ~ m1_subset_1(B_47,u1_struct_0(A_35))
      | ~ l1_orders_2(A_35)
      | ~ v3_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4676,plain,(
    ! [A_5990,B_5991,C_5992] :
      ( ~ r1_orders_2(A_5990,B_5991,C_5992)
      | m1_subset_1('#skF_5'(A_5990,B_5991,C_5992),k1_zfmisc_1(u1_struct_0(A_5990)))
      | ~ m1_subset_1(C_5992,u1_struct_0(A_5990))
      | ~ m1_subset_1(B_5991,u1_struct_0(A_5990))
      | ~ l1_orders_2(A_5990)
      | ~ v3_orders_2(A_5990) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_85097,plain,(
    ! [A_26890,A_26891,B_26892,C_26893] :
      ( ~ v1_xboole_0(u1_struct_0(A_26890))
      | ~ r2_hidden(A_26891,'#skF_5'(A_26890,B_26892,C_26893))
      | ~ r1_orders_2(A_26890,B_26892,C_26893)
      | ~ m1_subset_1(C_26893,u1_struct_0(A_26890))
      | ~ m1_subset_1(B_26892,u1_struct_0(A_26890))
      | ~ l1_orders_2(A_26890)
      | ~ v3_orders_2(A_26890) ) ),
    inference(resolution,[status(thm)],[c_4676,c_22])).

tff(c_85145,plain,(
    ! [A_27137,B_27138,C_27139] :
      ( ~ v1_xboole_0(u1_struct_0(A_27137))
      | ~ r1_orders_2(A_27137,B_27138,C_27139)
      | ~ m1_subset_1(C_27139,u1_struct_0(A_27137))
      | ~ m1_subset_1(B_27138,u1_struct_0(A_27137))
      | ~ l1_orders_2(A_27137)
      | ~ v3_orders_2(A_27137) ) ),
    inference(resolution,[status(thm)],[c_50,c_85097])).

tff(c_85147,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_150,c_85145])).

tff(c_85153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_135,c_85147])).

tff(c_85155,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_134,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_126])).

tff(c_85161,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_85155,c_134])).

tff(c_85196,plain,(
    ! [A_27396,B_27397] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_27396),B_27397),k1_zfmisc_1(u1_struct_0(A_27396)))
      | ~ m1_subset_1(B_27397,u1_struct_0(A_27396))
      | ~ l1_orders_2(A_27396)
      | ~ v3_orders_2(A_27396)
      | v2_struct_0(A_27396) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_85204,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_85161,c_85196])).

tff(c_85211,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_85204])).

tff(c_85212,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_85211])).

tff(c_86699,plain,(
    ! [A_31219,B_31220] :
      ( k1_orders_2(A_31219,B_31220) = a_2_0_orders_2(A_31219,B_31220)
      | ~ m1_subset_1(B_31220,k1_zfmisc_1(u1_struct_0(A_31219)))
      | ~ l1_orders_2(A_31219)
      | ~ v5_orders_2(A_31219)
      | ~ v4_orders_2(A_31219)
      | ~ v3_orders_2(A_31219)
      | v2_struct_0(A_31219) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86711,plain,
    ( k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_85212,c_86699])).

tff(c_86721,plain,
    ( k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_86711])).

tff(c_86722,plain,(
    k1_orders_2('#skF_6',k1_tarski('#skF_7')) = a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_86721])).

tff(c_84,plain,
    ( r2_orders_2('#skF_6','#skF_7','#skF_8')
    | r2_hidden('#skF_8',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_85160,plain,(
    r2_hidden('#skF_8',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_84])).

tff(c_85162,plain,(
    r2_hidden('#skF_8',k1_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85161,c_85160])).

tff(c_86780,plain,(
    r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86722,c_85162])).

tff(c_91868,plain,(
    ! [A_35209,B_35210,C_35211] :
      ( '#skF_3'(A_35209,B_35210,C_35211) = A_35209
      | ~ r2_hidden(A_35209,a_2_0_orders_2(B_35210,C_35211))
      | ~ m1_subset_1(C_35211,k1_zfmisc_1(u1_struct_0(B_35210)))
      | ~ l1_orders_2(B_35210)
      | ~ v5_orders_2(B_35210)
      | ~ v4_orders_2(B_35210)
      | ~ v3_orders_2(B_35210)
      | v2_struct_0(B_35210) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_91875,plain,
    ( '#skF_3'('#skF_8','#skF_6',k1_tarski('#skF_7')) = '#skF_8'
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_86780,c_91868])).

tff(c_91889,plain,
    ( '#skF_3'('#skF_8','#skF_6',k1_tarski('#skF_7')) = '#skF_8'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_85212,c_91875])).

tff(c_91890,plain,(
    '#skF_3'('#skF_8','#skF_6',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_91889])).

tff(c_179499,plain,(
    ! [B_59480,E_59481,A_59482,C_59483] :
      ( r2_orders_2(B_59480,E_59481,'#skF_3'(A_59482,B_59480,C_59483))
      | ~ r2_hidden(E_59481,C_59483)
      | ~ m1_subset_1(E_59481,u1_struct_0(B_59480))
      | ~ r2_hidden(A_59482,a_2_0_orders_2(B_59480,C_59483))
      | ~ m1_subset_1(C_59483,k1_zfmisc_1(u1_struct_0(B_59480)))
      | ~ l1_orders_2(B_59480)
      | ~ v5_orders_2(B_59480)
      | ~ v4_orders_2(B_59480)
      | ~ v3_orders_2(B_59480)
      | v2_struct_0(B_59480) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_179639,plain,(
    ! [E_59481,A_59482] :
      ( r2_orders_2('#skF_6',E_59481,'#skF_3'(A_59482,'#skF_6',k1_tarski('#skF_7')))
      | ~ r2_hidden(E_59481,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_59481,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_59482,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_85212,c_179499])).

tff(c_179650,plain,(
    ! [E_59481,A_59482] :
      ( r2_orders_2('#skF_6',E_59481,'#skF_3'(A_59482,'#skF_6',k1_tarski('#skF_7')))
      | ~ r2_hidden(E_59481,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_59481,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_59482,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_179639])).

tff(c_180520,plain,(
    ! [E_59972,A_59973] :
      ( r2_orders_2('#skF_6',E_59972,'#skF_3'(A_59973,'#skF_6',k1_tarski('#skF_7')))
      | ~ r2_hidden(E_59972,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_59972,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_59973,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_179650])).

tff(c_181363,plain,(
    ! [E_59972] :
      ( r2_orders_2('#skF_6',E_59972,'#skF_8')
      | ~ r2_hidden(E_59972,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_59972,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91890,c_180520])).

tff(c_181407,plain,(
    ! [E_60217] :
      ( r2_orders_2('#skF_6',E_60217,'#skF_8')
      | ~ r2_hidden(E_60217,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_60217,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86780,c_181363])).

tff(c_181630,plain,
    ( r2_orders_2('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_97,c_181407])).

tff(c_181636,plain,(
    r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_181630])).

tff(c_181638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_181636])).

tff(c_181639,plain,(
    ~ r2_hidden('#skF_8',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_240044,plain,(
    ~ r2_hidden('#skF_8',k1_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240037,c_181639])).

tff(c_241619,plain,(
    ~ r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241561,c_240044])).

tff(c_181640,plain,(
    r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_244052,plain,(
    ! [D_88439,B_88440,C_88441] :
      ( r2_hidden('#skF_4'(D_88439,B_88440,C_88441,D_88439),C_88441)
      | r2_hidden(D_88439,a_2_0_orders_2(B_88440,C_88441))
      | ~ m1_subset_1(D_88439,u1_struct_0(B_88440))
      | ~ m1_subset_1(C_88441,k1_zfmisc_1(u1_struct_0(B_88440)))
      | ~ l1_orders_2(B_88440)
      | ~ v5_orders_2(B_88440)
      | ~ v4_orders_2(B_88440)
      | ~ v3_orders_2(B_88440)
      | v2_struct_0(B_88440) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_244066,plain,(
    ! [D_88439] :
      ( r2_hidden('#skF_4'(D_88439,'#skF_6',k1_tarski('#skF_7'),D_88439),k1_tarski('#skF_7'))
      | r2_hidden(D_88439,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_88439,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_240081,c_244052])).

tff(c_244077,plain,(
    ! [D_88439] :
      ( r2_hidden('#skF_4'(D_88439,'#skF_6',k1_tarski('#skF_7'),D_88439),k1_tarski('#skF_7'))
      | r2_hidden(D_88439,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_88439,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_244066])).

tff(c_244297,plain,(
    ! [D_88690] :
      ( r2_hidden('#skF_4'(D_88690,'#skF_6',k1_tarski('#skF_7'),D_88690),k1_tarski('#skF_7'))
      | r2_hidden(D_88690,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_88690,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_244077])).

tff(c_181658,plain,(
    ! [D_60467,B_60468,A_60469] :
      ( D_60467 = B_60468
      | D_60467 = A_60469
      | ~ r2_hidden(D_60467,k2_tarski(A_60469,B_60468)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_181667,plain,(
    ! [D_60467,A_7] :
      ( D_60467 = A_7
      | D_60467 = A_7
      | ~ r2_hidden(D_60467,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_181658])).

tff(c_244391,plain,(
    ! [D_88772] :
      ( '#skF_4'(D_88772,'#skF_6',k1_tarski('#skF_7'),D_88772) = '#skF_7'
      | r2_hidden(D_88772,a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_88772,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_244297,c_181667])).

tff(c_244410,plain,
    ( '#skF_4'('#skF_8','#skF_6',k1_tarski('#skF_7'),'#skF_8') = '#skF_7'
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_244391,c_241619])).

tff(c_244509,plain,(
    '#skF_4'('#skF_8','#skF_6',k1_tarski('#skF_7'),'#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_244410])).

tff(c_26,plain,(
    ! [B_15,D_25,C_16] :
      ( ~ r2_orders_2(B_15,'#skF_4'(D_25,B_15,C_16,D_25),D_25)
      | r2_hidden(D_25,a_2_0_orders_2(B_15,C_16))
      | ~ m1_subset_1(D_25,u1_struct_0(B_15))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(B_15)))
      | ~ l1_orders_2(B_15)
      | ~ v5_orders_2(B_15)
      | ~ v4_orders_2(B_15)
      | ~ v3_orders_2(B_15)
      | v2_struct_0(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_244517,plain,
    ( ~ r2_orders_2('#skF_6','#skF_7','#skF_8')
    | r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_244509,c_26])).

tff(c_244562,plain,
    ( r2_hidden('#skF_8',a_2_0_orders_2('#skF_6',k1_tarski('#skF_7')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_240081,c_64,c_181640,c_244517])).

tff(c_244564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_241619,c_244562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.89/24.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.89/24.31  
% 36.89/24.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.89/24.31  %$ r2_orders_2 > r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 36.89/24.31  
% 36.89/24.31  %Foreground sorts:
% 36.89/24.31  
% 36.89/24.31  
% 36.89/24.31  %Background operators:
% 36.89/24.31  
% 36.89/24.31  
% 36.89/24.31  %Foreground operators:
% 36.89/24.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 36.89/24.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 36.89/24.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 36.89/24.31  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 36.89/24.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.89/24.31  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 36.89/24.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.89/24.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.89/24.31  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 36.89/24.31  tff('#skF_7', type, '#skF_7': $i).
% 36.89/24.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 36.89/24.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.89/24.31  tff('#skF_6', type, '#skF_6': $i).
% 36.89/24.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 36.89/24.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 36.89/24.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 36.89/24.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 36.89/24.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 36.89/24.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 36.89/24.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 36.89/24.31  tff('#skF_8', type, '#skF_8': $i).
% 36.89/24.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.89/24.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 36.89/24.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.89/24.31  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 36.89/24.31  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 36.89/24.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 36.89/24.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 36.89/24.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 36.89/24.31  
% 36.89/24.33  tff(f_182, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(C, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_orders_2)).
% 36.89/24.33  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 36.89/24.33  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 36.89/24.33  tff(f_160, axiom, (![A]: ((v3_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~(((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) & ~r1_orders_2(A, B, C)) & ~r1_orders_2(A, C, B)) & ~((r1_orders_2(A, B, C) | r1_orders_2(A, C, B)) & (![D]: ((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~(r2_hidden(B, D) & r2_hidden(C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_orders_2)).
% 36.89/24.33  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 36.89/24.33  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 36.89/24.33  tff(f_59, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 36.89/24.33  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 36.89/24.33  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 36.89/24.33  tff(f_86, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 36.89/24.33  tff(c_76, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_74, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_72, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_70, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_68, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_66, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_181679, plain, (![A_60475, B_60476]: (k6_domain_1(A_60475, B_60476)=k1_tarski(B_60476) | ~m1_subset_1(B_60476, A_60475) | v1_xboole_0(A_60475))), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.89/24.33  tff(c_181687, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_181679])).
% 36.89/24.33  tff(c_181701, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_181687])).
% 36.89/24.33  tff(c_181688, plain, (![A_60477, B_60478]: (r1_orders_2(A_60477, B_60478, B_60478) | ~m1_subset_1(B_60478, u1_struct_0(A_60477)) | ~l1_orders_2(A_60477) | ~v3_orders_2(A_60477) | v2_struct_0(A_60477))), inference(cnfTransformation, [status(thm)], [f_105])).
% 36.89/24.33  tff(c_181692, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_181688])).
% 36.89/24.33  tff(c_181699, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_181692])).
% 36.89/24.33  tff(c_181700, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_76, c_181699])).
% 36.89/24.33  tff(c_48, plain, (![A_35, C_53, B_47]: (~r1_orders_2(A_35, C_53, B_47) | r2_hidden(C_53, '#skF_5'(A_35, B_47, C_53)) | ~m1_subset_1(C_53, u1_struct_0(A_35)) | ~m1_subset_1(B_47, u1_struct_0(A_35)) | ~l1_orders_2(A_35) | ~v3_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_160])).
% 36.89/24.33  tff(c_185071, plain, (![A_65096, C_65097, B_65098]: (~r1_orders_2(A_65096, C_65097, B_65098) | m1_subset_1('#skF_5'(A_65096, B_65098, C_65097), k1_zfmisc_1(u1_struct_0(A_65096))) | ~m1_subset_1(C_65097, u1_struct_0(A_65096)) | ~m1_subset_1(B_65098, u1_struct_0(A_65096)) | ~l1_orders_2(A_65096) | ~v3_orders_2(A_65096))), inference(cnfTransformation, [status(thm)], [f_160])).
% 36.89/24.33  tff(c_22, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.89/24.33  tff(c_239980, plain, (![A_81534, A_81535, B_81536, C_81537]: (~v1_xboole_0(u1_struct_0(A_81534)) | ~r2_hidden(A_81535, '#skF_5'(A_81534, B_81536, C_81537)) | ~r1_orders_2(A_81534, C_81537, B_81536) | ~m1_subset_1(C_81537, u1_struct_0(A_81534)) | ~m1_subset_1(B_81536, u1_struct_0(A_81534)) | ~l1_orders_2(A_81534) | ~v3_orders_2(A_81534))), inference(resolution, [status(thm)], [c_185071, c_22])).
% 36.89/24.33  tff(c_240028, plain, (![A_81781, C_81782, B_81783]: (~v1_xboole_0(u1_struct_0(A_81781)) | ~r1_orders_2(A_81781, C_81782, B_81783) | ~m1_subset_1(C_81782, u1_struct_0(A_81781)) | ~m1_subset_1(B_81783, u1_struct_0(A_81781)) | ~l1_orders_2(A_81781) | ~v3_orders_2(A_81781))), inference(resolution, [status(thm)], [c_48, c_239980])).
% 36.89/24.33  tff(c_240030, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_181700, c_240028])).
% 36.89/24.33  tff(c_240036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_181701, c_240030])).
% 36.89/24.33  tff(c_240037, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_181687])).
% 36.89/24.33  tff(c_240065, plain, (![A_82038, B_82039]: (m1_subset_1(k6_domain_1(u1_struct_0(A_82038), B_82039), k1_zfmisc_1(u1_struct_0(A_82038))) | ~m1_subset_1(B_82039, u1_struct_0(A_82038)) | ~l1_orders_2(A_82038) | ~v3_orders_2(A_82038) | v2_struct_0(A_82038))), inference(cnfTransformation, [status(thm)], [f_119])).
% 36.89/24.33  tff(c_240073, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_240037, c_240065])).
% 36.89/24.33  tff(c_240080, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_240073])).
% 36.89/24.33  tff(c_240081, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_240080])).
% 36.89/24.33  tff(c_241538, plain, (![A_85780, B_85781]: (k1_orders_2(A_85780, B_85781)=a_2_0_orders_2(A_85780, B_85781) | ~m1_subset_1(B_85781, k1_zfmisc_1(u1_struct_0(A_85780))) | ~l1_orders_2(A_85780) | ~v5_orders_2(A_85780) | ~v4_orders_2(A_85780) | ~v3_orders_2(A_85780) | v2_struct_0(A_85780))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.89/24.33  tff(c_241550, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_240081, c_241538])).
% 36.89/24.33  tff(c_241560, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_241550])).
% 36.89/24.33  tff(c_241561, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_76, c_241560])).
% 36.89/24.33  tff(c_78, plain, (~r2_hidden('#skF_8', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'))) | ~r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_98, plain, (~r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 36.89/24.33  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 36.89/24.33  tff(c_94, plain, (![D_62, B_63]: (r2_hidden(D_62, k2_tarski(D_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.89/24.33  tff(c_97, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 36.89/24.33  tff(c_64, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_126, plain, (![A_75, B_76]: (k6_domain_1(A_75, B_76)=k1_tarski(B_76) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.89/24.33  tff(c_133, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_126])).
% 36.89/24.33  tff(c_135, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_133])).
% 36.89/24.33  tff(c_138, plain, (![A_77, B_78]: (r1_orders_2(A_77, B_78, B_78) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_105])).
% 36.89/24.33  tff(c_142, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_138])).
% 36.89/24.33  tff(c_149, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_142])).
% 36.89/24.33  tff(c_150, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_76, c_149])).
% 36.89/24.33  tff(c_50, plain, (![A_35, B_47, C_53]: (~r1_orders_2(A_35, B_47, C_53) | r2_hidden(C_53, '#skF_5'(A_35, B_47, C_53)) | ~m1_subset_1(C_53, u1_struct_0(A_35)) | ~m1_subset_1(B_47, u1_struct_0(A_35)) | ~l1_orders_2(A_35) | ~v3_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_160])).
% 36.89/24.33  tff(c_4676, plain, (![A_5990, B_5991, C_5992]: (~r1_orders_2(A_5990, B_5991, C_5992) | m1_subset_1('#skF_5'(A_5990, B_5991, C_5992), k1_zfmisc_1(u1_struct_0(A_5990))) | ~m1_subset_1(C_5992, u1_struct_0(A_5990)) | ~m1_subset_1(B_5991, u1_struct_0(A_5990)) | ~l1_orders_2(A_5990) | ~v3_orders_2(A_5990))), inference(cnfTransformation, [status(thm)], [f_160])).
% 36.89/24.33  tff(c_85097, plain, (![A_26890, A_26891, B_26892, C_26893]: (~v1_xboole_0(u1_struct_0(A_26890)) | ~r2_hidden(A_26891, '#skF_5'(A_26890, B_26892, C_26893)) | ~r1_orders_2(A_26890, B_26892, C_26893) | ~m1_subset_1(C_26893, u1_struct_0(A_26890)) | ~m1_subset_1(B_26892, u1_struct_0(A_26890)) | ~l1_orders_2(A_26890) | ~v3_orders_2(A_26890))), inference(resolution, [status(thm)], [c_4676, c_22])).
% 36.89/24.33  tff(c_85145, plain, (![A_27137, B_27138, C_27139]: (~v1_xboole_0(u1_struct_0(A_27137)) | ~r1_orders_2(A_27137, B_27138, C_27139) | ~m1_subset_1(C_27139, u1_struct_0(A_27137)) | ~m1_subset_1(B_27138, u1_struct_0(A_27137)) | ~l1_orders_2(A_27137) | ~v3_orders_2(A_27137))), inference(resolution, [status(thm)], [c_50, c_85097])).
% 36.89/24.33  tff(c_85147, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_150, c_85145])).
% 36.89/24.33  tff(c_85153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_135, c_85147])).
% 36.89/24.33  tff(c_85155, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_133])).
% 36.89/24.33  tff(c_134, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_126])).
% 36.89/24.33  tff(c_85161, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_85155, c_134])).
% 36.89/24.33  tff(c_85196, plain, (![A_27396, B_27397]: (m1_subset_1(k6_domain_1(u1_struct_0(A_27396), B_27397), k1_zfmisc_1(u1_struct_0(A_27396))) | ~m1_subset_1(B_27397, u1_struct_0(A_27396)) | ~l1_orders_2(A_27396) | ~v3_orders_2(A_27396) | v2_struct_0(A_27396))), inference(cnfTransformation, [status(thm)], [f_119])).
% 36.89/24.33  tff(c_85204, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_85161, c_85196])).
% 36.89/24.33  tff(c_85211, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_85204])).
% 36.89/24.33  tff(c_85212, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_85211])).
% 36.89/24.33  tff(c_86699, plain, (![A_31219, B_31220]: (k1_orders_2(A_31219, B_31220)=a_2_0_orders_2(A_31219, B_31220) | ~m1_subset_1(B_31220, k1_zfmisc_1(u1_struct_0(A_31219))) | ~l1_orders_2(A_31219) | ~v5_orders_2(A_31219) | ~v4_orders_2(A_31219) | ~v3_orders_2(A_31219) | v2_struct_0(A_31219))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.89/24.33  tff(c_86711, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_85212, c_86699])).
% 36.89/24.33  tff(c_86721, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_86711])).
% 36.89/24.33  tff(c_86722, plain, (k1_orders_2('#skF_6', k1_tarski('#skF_7'))=a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_76, c_86721])).
% 36.89/24.33  tff(c_84, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8') | r2_hidden('#skF_8', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 36.89/24.33  tff(c_85160, plain, (r2_hidden('#skF_8', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_98, c_84])).
% 36.89/24.33  tff(c_85162, plain, (r2_hidden('#skF_8', k1_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_85161, c_85160])).
% 36.89/24.33  tff(c_86780, plain, (r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_86722, c_85162])).
% 36.89/24.33  tff(c_91868, plain, (![A_35209, B_35210, C_35211]: ('#skF_3'(A_35209, B_35210, C_35211)=A_35209 | ~r2_hidden(A_35209, a_2_0_orders_2(B_35210, C_35211)) | ~m1_subset_1(C_35211, k1_zfmisc_1(u1_struct_0(B_35210))) | ~l1_orders_2(B_35210) | ~v5_orders_2(B_35210) | ~v4_orders_2(B_35210) | ~v3_orders_2(B_35210) | v2_struct_0(B_35210))), inference(cnfTransformation, [status(thm)], [f_86])).
% 36.89/24.33  tff(c_91875, plain, ('#skF_3'('#skF_8', '#skF_6', k1_tarski('#skF_7'))='#skF_8' | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_86780, c_91868])).
% 36.89/24.33  tff(c_91889, plain, ('#skF_3'('#skF_8', '#skF_6', k1_tarski('#skF_7'))='#skF_8' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_85212, c_91875])).
% 36.89/24.33  tff(c_91890, plain, ('#skF_3'('#skF_8', '#skF_6', k1_tarski('#skF_7'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_76, c_91889])).
% 36.89/24.33  tff(c_179499, plain, (![B_59480, E_59481, A_59482, C_59483]: (r2_orders_2(B_59480, E_59481, '#skF_3'(A_59482, B_59480, C_59483)) | ~r2_hidden(E_59481, C_59483) | ~m1_subset_1(E_59481, u1_struct_0(B_59480)) | ~r2_hidden(A_59482, a_2_0_orders_2(B_59480, C_59483)) | ~m1_subset_1(C_59483, k1_zfmisc_1(u1_struct_0(B_59480))) | ~l1_orders_2(B_59480) | ~v5_orders_2(B_59480) | ~v4_orders_2(B_59480) | ~v3_orders_2(B_59480) | v2_struct_0(B_59480))), inference(cnfTransformation, [status(thm)], [f_86])).
% 36.89/24.33  tff(c_179639, plain, (![E_59481, A_59482]: (r2_orders_2('#skF_6', E_59481, '#skF_3'(A_59482, '#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden(E_59481, k1_tarski('#skF_7')) | ~m1_subset_1(E_59481, u1_struct_0('#skF_6')) | ~r2_hidden(A_59482, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_85212, c_179499])).
% 36.89/24.33  tff(c_179650, plain, (![E_59481, A_59482]: (r2_orders_2('#skF_6', E_59481, '#skF_3'(A_59482, '#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden(E_59481, k1_tarski('#skF_7')) | ~m1_subset_1(E_59481, u1_struct_0('#skF_6')) | ~r2_hidden(A_59482, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_179639])).
% 36.89/24.33  tff(c_180520, plain, (![E_59972, A_59973]: (r2_orders_2('#skF_6', E_59972, '#skF_3'(A_59973, '#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden(E_59972, k1_tarski('#skF_7')) | ~m1_subset_1(E_59972, u1_struct_0('#skF_6')) | ~r2_hidden(A_59973, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_179650])).
% 36.89/24.33  tff(c_181363, plain, (![E_59972]: (r2_orders_2('#skF_6', E_59972, '#skF_8') | ~r2_hidden(E_59972, k1_tarski('#skF_7')) | ~m1_subset_1(E_59972, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_91890, c_180520])).
% 36.89/24.33  tff(c_181407, plain, (![E_60217]: (r2_orders_2('#skF_6', E_60217, '#skF_8') | ~r2_hidden(E_60217, k1_tarski('#skF_7')) | ~m1_subset_1(E_60217, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_86780, c_181363])).
% 36.89/24.33  tff(c_181630, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_97, c_181407])).
% 36.89/24.33  tff(c_181636, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_181630])).
% 36.89/24.33  tff(c_181638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_181636])).
% 36.89/24.33  tff(c_181639, plain, (~r2_hidden('#skF_8', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')))), inference(splitRight, [status(thm)], [c_78])).
% 36.89/24.33  tff(c_240044, plain, (~r2_hidden('#skF_8', k1_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_240037, c_181639])).
% 36.89/24.33  tff(c_241619, plain, (~r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_241561, c_240044])).
% 36.89/24.33  tff(c_181640, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 36.89/24.33  tff(c_244052, plain, (![D_88439, B_88440, C_88441]: (r2_hidden('#skF_4'(D_88439, B_88440, C_88441, D_88439), C_88441) | r2_hidden(D_88439, a_2_0_orders_2(B_88440, C_88441)) | ~m1_subset_1(D_88439, u1_struct_0(B_88440)) | ~m1_subset_1(C_88441, k1_zfmisc_1(u1_struct_0(B_88440))) | ~l1_orders_2(B_88440) | ~v5_orders_2(B_88440) | ~v4_orders_2(B_88440) | ~v3_orders_2(B_88440) | v2_struct_0(B_88440))), inference(cnfTransformation, [status(thm)], [f_86])).
% 36.89/24.33  tff(c_244066, plain, (![D_88439]: (r2_hidden('#skF_4'(D_88439, '#skF_6', k1_tarski('#skF_7'), D_88439), k1_tarski('#skF_7')) | r2_hidden(D_88439, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(D_88439, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_240081, c_244052])).
% 36.89/24.33  tff(c_244077, plain, (![D_88439]: (r2_hidden('#skF_4'(D_88439, '#skF_6', k1_tarski('#skF_7'), D_88439), k1_tarski('#skF_7')) | r2_hidden(D_88439, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(D_88439, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_244066])).
% 36.89/24.33  tff(c_244297, plain, (![D_88690]: (r2_hidden('#skF_4'(D_88690, '#skF_6', k1_tarski('#skF_7'), D_88690), k1_tarski('#skF_7')) | r2_hidden(D_88690, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(D_88690, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_244077])).
% 36.89/24.33  tff(c_181658, plain, (![D_60467, B_60468, A_60469]: (D_60467=B_60468 | D_60467=A_60469 | ~r2_hidden(D_60467, k2_tarski(A_60469, B_60468)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.89/24.33  tff(c_181667, plain, (![D_60467, A_7]: (D_60467=A_7 | D_60467=A_7 | ~r2_hidden(D_60467, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_181658])).
% 36.89/24.33  tff(c_244391, plain, (![D_88772]: ('#skF_4'(D_88772, '#skF_6', k1_tarski('#skF_7'), D_88772)='#skF_7' | r2_hidden(D_88772, a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1(D_88772, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_244297, c_181667])).
% 36.89/24.33  tff(c_244410, plain, ('#skF_4'('#skF_8', '#skF_6', k1_tarski('#skF_7'), '#skF_8')='#skF_7' | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_244391, c_241619])).
% 36.89/24.33  tff(c_244509, plain, ('#skF_4'('#skF_8', '#skF_6', k1_tarski('#skF_7'), '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_244410])).
% 36.89/24.33  tff(c_26, plain, (![B_15, D_25, C_16]: (~r2_orders_2(B_15, '#skF_4'(D_25, B_15, C_16, D_25), D_25) | r2_hidden(D_25, a_2_0_orders_2(B_15, C_16)) | ~m1_subset_1(D_25, u1_struct_0(B_15)) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0(B_15))) | ~l1_orders_2(B_15) | ~v5_orders_2(B_15) | ~v4_orders_2(B_15) | ~v3_orders_2(B_15) | v2_struct_0(B_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 36.89/24.33  tff(c_244517, plain, (~r2_orders_2('#skF_6', '#skF_7', '#skF_8') | r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_244509, c_26])).
% 36.89/24.33  tff(c_244562, plain, (r2_hidden('#skF_8', a_2_0_orders_2('#skF_6', k1_tarski('#skF_7'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_240081, c_64, c_181640, c_244517])).
% 36.89/24.33  tff(c_244564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_241619, c_244562])).
% 36.89/24.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.89/24.33  
% 36.89/24.33  Inference rules
% 36.89/24.33  ----------------------
% 36.89/24.33  #Ref     : 0
% 36.89/24.33  #Sup     : 28655
% 36.89/24.33  #Fact    : 172
% 36.89/24.33  #Define  : 0
% 36.89/24.33  #Split   : 31
% 36.89/24.33  #Chain   : 0
% 36.89/24.33  #Close   : 0
% 36.89/24.33  
% 36.89/24.33  Ordering : KBO
% 36.89/24.33  
% 36.89/24.33  Simplification rules
% 36.89/24.33  ----------------------
% 36.89/24.33  #Subsume      : 2281
% 36.89/24.33  #Demod        : 1981
% 36.89/24.33  #Tautology    : 1612
% 36.89/24.33  #SimpNegUnit  : 65
% 36.89/24.33  #BackRed      : 4
% 36.89/24.33  
% 36.89/24.33  #Partial instantiations: 48960
% 36.89/24.33  #Strategies tried      : 1
% 36.89/24.33  
% 36.89/24.33  Timing (in seconds)
% 36.89/24.33  ----------------------
% 36.89/24.33  Preprocessing        : 0.38
% 36.89/24.33  Parsing              : 0.20
% 36.89/24.33  CNF conversion       : 0.03
% 36.89/24.33  Main loop            : 23.14
% 36.89/24.33  Inferencing          : 6.26
% 36.89/24.33  Reduction            : 3.31
% 36.89/24.33  Demodulation         : 2.34
% 36.89/24.34  BG Simplification    : 1.23
% 36.89/24.34  Subsumption          : 11.65
% 36.89/24.34  Abstraction          : 1.86
% 36.89/24.34  MUC search           : 0.00
% 36.89/24.34  Cooper               : 0.00
% 36.89/24.34  Total                : 23.57
% 36.89/24.34  Index Insertion      : 0.00
% 36.89/24.34  Index Deletion       : 0.00
% 36.89/24.34  Index Matching       : 0.00
% 36.89/24.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
