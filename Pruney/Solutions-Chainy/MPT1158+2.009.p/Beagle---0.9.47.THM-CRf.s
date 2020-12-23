%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:43 EST 2020

% Result     : Theorem 38.52s
% Output     : CNFRefutation 38.60s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 451 expanded)
%              Number of leaves         :   39 ( 182 expanded)
%              Depth                    :   18
%              Number of atoms          :  356 (1852 expanded)
%              Number of equality atoms :   33 (  99 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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
                <=> r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

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

tff(c_64,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_182136,plain,(
    ! [A_60471,B_60472] :
      ( k6_domain_1(A_60471,B_60472) = k1_tarski(B_60472)
      | ~ m1_subset_1(B_60472,A_60471)
      | v1_xboole_0(A_60471) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_182143,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_182136])).

tff(c_182145,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_182143])).

tff(c_182147,plain,(
    ! [A_60473,B_60474] :
      ( r1_orders_2(A_60473,B_60474,B_60474)
      | ~ m1_subset_1(B_60474,u1_struct_0(A_60473))
      | ~ l1_orders_2(A_60473)
      | ~ v3_orders_2(A_60473)
      | v2_struct_0(A_60473) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_182151,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_182147])).

tff(c_182158,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_182151])).

tff(c_182159,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_182158])).

tff(c_50,plain,(
    ! [A_35,B_47,C_53] :
      ( ~ r1_orders_2(A_35,B_47,C_53)
      | r2_hidden(C_53,'#skF_5'(A_35,B_47,C_53))
      | ~ m1_subset_1(C_53,u1_struct_0(A_35))
      | ~ m1_subset_1(B_47,u1_struct_0(A_35))
      | ~ l1_orders_2(A_35)
      | ~ v3_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_184923,plain,(
    ! [A_64759,B_64760,C_64761] :
      ( ~ r1_orders_2(A_64759,B_64760,C_64761)
      | m1_subset_1('#skF_5'(A_64759,B_64760,C_64761),k1_zfmisc_1(u1_struct_0(A_64759)))
      | ~ m1_subset_1(C_64761,u1_struct_0(A_64759))
      | ~ m1_subset_1(B_64760,u1_struct_0(A_64759))
      | ~ l1_orders_2(A_64759)
      | ~ v3_orders_2(A_64759) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_22,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_188863,plain,(
    ! [A_67185,A_67186,B_67187,C_67188] :
      ( ~ v1_xboole_0(u1_struct_0(A_67185))
      | ~ r2_hidden(A_67186,'#skF_5'(A_67185,B_67187,C_67188))
      | ~ r1_orders_2(A_67185,B_67187,C_67188)
      | ~ m1_subset_1(C_67188,u1_struct_0(A_67185))
      | ~ m1_subset_1(B_67187,u1_struct_0(A_67185))
      | ~ l1_orders_2(A_67185)
      | ~ v3_orders_2(A_67185) ) ),
    inference(resolution,[status(thm)],[c_184923,c_22])).

tff(c_188893,plain,(
    ! [A_67270,B_67271,C_67272] :
      ( ~ v1_xboole_0(u1_struct_0(A_67270))
      | ~ r1_orders_2(A_67270,B_67271,C_67272)
      | ~ m1_subset_1(C_67272,u1_struct_0(A_67270))
      | ~ m1_subset_1(B_67271,u1_struct_0(A_67270))
      | ~ l1_orders_2(A_67270)
      | ~ v3_orders_2(A_67270) ) ),
    inference(resolution,[status(thm)],[c_50,c_188863])).

tff(c_188895,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_182159,c_188893])).

tff(c_188901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_182145,c_188895])).

tff(c_188902,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_182143])).

tff(c_188943,plain,(
    ! [A_67367,B_67368] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_67367),B_67368),k1_zfmisc_1(u1_struct_0(A_67367)))
      | ~ m1_subset_1(B_67368,u1_struct_0(A_67367))
      | ~ l1_orders_2(A_67367)
      | ~ v3_orders_2(A_67367)
      | v2_struct_0(A_67367) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_188954,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_188902,c_188943])).

tff(c_188961,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_64,c_188954])).

tff(c_188962,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_188961])).

tff(c_190542,plain,(
    ! [A_71439,B_71440] :
      ( k2_orders_2(A_71439,B_71440) = a_2_1_orders_2(A_71439,B_71440)
      | ~ m1_subset_1(B_71440,k1_zfmisc_1(u1_struct_0(A_71439)))
      | ~ l1_orders_2(A_71439)
      | ~ v5_orders_2(A_71439)
      | ~ v4_orders_2(A_71439)
      | ~ v3_orders_2(A_71439)
      | v2_struct_0(A_71439) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_190551,plain,
    ( k2_orders_2('#skF_6',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_6',k1_tarski('#skF_8'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_188962,c_190542])).

tff(c_190560,plain,
    ( k2_orders_2('#skF_6',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_6',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_190551])).

tff(c_190561,plain,(
    k2_orders_2('#skF_6',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_190560])).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_7',k2_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_8')))
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

tff(c_4676,plain,(
    ! [A_5990,B_5991,C_5992] :
      ( ~ r1_orders_2(A_5990,B_5991,C_5992)
      | m1_subset_1('#skF_5'(A_5990,B_5991,C_5992),k1_zfmisc_1(u1_struct_0(A_5990)))
      | ~ m1_subset_1(C_5992,u1_struct_0(A_5990))
      | ~ m1_subset_1(B_5991,u1_struct_0(A_5990))
      | ~ l1_orders_2(A_5990)
      | ~ v3_orders_2(A_5990) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_85013,plain,(
    ! [A_26890,A_26891,B_26892,C_26893] :
      ( ~ v1_xboole_0(u1_struct_0(A_26890))
      | ~ r2_hidden(A_26891,'#skF_5'(A_26890,B_26892,C_26893))
      | ~ r1_orders_2(A_26890,B_26892,C_26893)
      | ~ m1_subset_1(C_26893,u1_struct_0(A_26890))
      | ~ m1_subset_1(B_26892,u1_struct_0(A_26890))
      | ~ l1_orders_2(A_26890)
      | ~ v3_orders_2(A_26890) ) ),
    inference(resolution,[status(thm)],[c_4676,c_22])).

tff(c_85061,plain,(
    ! [A_27137,B_27138,C_27139] :
      ( ~ v1_xboole_0(u1_struct_0(A_27137))
      | ~ r1_orders_2(A_27137,B_27138,C_27139)
      | ~ m1_subset_1(C_27139,u1_struct_0(A_27137))
      | ~ m1_subset_1(B_27138,u1_struct_0(A_27137))
      | ~ l1_orders_2(A_27137)
      | ~ v3_orders_2(A_27137) ) ),
    inference(resolution,[status(thm)],[c_50,c_85013])).

tff(c_85063,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_150,c_85061])).

tff(c_85069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_135,c_85063])).

tff(c_85070,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_85112,plain,(
    ! [A_27396,B_27397] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_27396),B_27397),k1_zfmisc_1(u1_struct_0(A_27396)))
      | ~ m1_subset_1(B_27397,u1_struct_0(A_27396))
      | ~ l1_orders_2(A_27396)
      | ~ v3_orders_2(A_27396)
      | v2_struct_0(A_27396) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_85123,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_85070,c_85112])).

tff(c_85130,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_64,c_85123])).

tff(c_85131,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_85130])).

tff(c_86615,plain,(
    ! [A_31219,B_31220] :
      ( k2_orders_2(A_31219,B_31220) = a_2_1_orders_2(A_31219,B_31220)
      | ~ m1_subset_1(B_31220,k1_zfmisc_1(u1_struct_0(A_31219)))
      | ~ l1_orders_2(A_31219)
      | ~ v5_orders_2(A_31219)
      | ~ v4_orders_2(A_31219)
      | ~ v3_orders_2(A_31219)
      | v2_struct_0(A_31219) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86624,plain,
    ( k2_orders_2('#skF_6',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_6',k1_tarski('#skF_8'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_85131,c_86615])).

tff(c_86633,plain,
    ( k2_orders_2('#skF_6',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_6',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_86624])).

tff(c_86634,plain,(
    k2_orders_2('#skF_6',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_86633])).

tff(c_84,plain,
    ( r2_orders_2('#skF_6','#skF_7','#skF_8')
    | r2_hidden('#skF_7',k2_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_85076,plain,
    ( r2_orders_2('#skF_6','#skF_7','#skF_8')
    | r2_hidden('#skF_7',k2_orders_2('#skF_6',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85070,c_84])).

tff(c_85077,plain,(
    r2_hidden('#skF_7',k2_orders_2('#skF_6',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_85076])).

tff(c_86640,plain,(
    r2_hidden('#skF_7',a_2_1_orders_2('#skF_6',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86634,c_85077])).

tff(c_91997,plain,(
    ! [A_35290,B_35291,C_35292] :
      ( '#skF_3'(A_35290,B_35291,C_35292) = A_35290
      | ~ r2_hidden(A_35290,a_2_1_orders_2(B_35291,C_35292))
      | ~ m1_subset_1(C_35292,k1_zfmisc_1(u1_struct_0(B_35291)))
      | ~ l1_orders_2(B_35291)
      | ~ v5_orders_2(B_35291)
      | ~ v4_orders_2(B_35291)
      | ~ v3_orders_2(B_35291)
      | v2_struct_0(B_35291) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_92004,plain,
    ( '#skF_3'('#skF_7','#skF_6',k1_tarski('#skF_8')) = '#skF_7'
    | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_86640,c_91997])).

tff(c_92018,plain,
    ( '#skF_3'('#skF_7','#skF_6',k1_tarski('#skF_8')) = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_85131,c_92004])).

tff(c_92019,plain,(
    '#skF_3'('#skF_7','#skF_6',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_92018])).

tff(c_180845,plain,(
    ! [B_59724,A_59725,C_59726,E_59727] :
      ( r2_orders_2(B_59724,'#skF_3'(A_59725,B_59724,C_59726),E_59727)
      | ~ r2_hidden(E_59727,C_59726)
      | ~ m1_subset_1(E_59727,u1_struct_0(B_59724))
      | ~ r2_hidden(A_59725,a_2_1_orders_2(B_59724,C_59726))
      | ~ m1_subset_1(C_59726,k1_zfmisc_1(u1_struct_0(B_59724)))
      | ~ l1_orders_2(B_59724)
      | ~ v5_orders_2(B_59724)
      | ~ v4_orders_2(B_59724)
      | ~ v3_orders_2(B_59724)
      | v2_struct_0(B_59724) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_180983,plain,(
    ! [A_59725,E_59727] :
      ( r2_orders_2('#skF_6','#skF_3'(A_59725,'#skF_6',k1_tarski('#skF_8')),E_59727)
      | ~ r2_hidden(E_59727,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_59727,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_59725,a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_85131,c_180845])).

tff(c_180992,plain,(
    ! [A_59725,E_59727] :
      ( r2_orders_2('#skF_6','#skF_3'(A_59725,'#skF_6',k1_tarski('#skF_8')),E_59727)
      | ~ r2_hidden(E_59727,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_59727,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_59725,a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_180983])).

tff(c_180999,plain,(
    ! [A_59971,E_59972] :
      ( r2_orders_2('#skF_6','#skF_3'(A_59971,'#skF_6',k1_tarski('#skF_8')),E_59972)
      | ~ r2_hidden(E_59972,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_59972,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_59971,a_2_1_orders_2('#skF_6',k1_tarski('#skF_8'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_180992])).

tff(c_181830,plain,(
    ! [E_59972] :
      ( r2_orders_2('#skF_6','#skF_7',E_59972)
      | ~ r2_hidden(E_59972,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_59972,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_7',a_2_1_orders_2('#skF_6',k1_tarski('#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92019,c_180999])).

tff(c_181874,plain,(
    ! [E_60216] :
      ( r2_orders_2('#skF_6','#skF_7',E_60216)
      | ~ r2_hidden(E_60216,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_60216,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86640,c_181830])).

tff(c_182097,plain,
    ( r2_orders_2('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_97,c_181874])).

tff(c_182103,plain,(
    r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_182097])).

tff(c_182105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_182103])).

tff(c_182106,plain,(
    ~ r2_hidden('#skF_7',k2_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_188904,plain,(
    ~ r2_hidden('#skF_7',k2_orders_2('#skF_6',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188902,c_182106])).

tff(c_190567,plain,(
    ~ r2_hidden('#skF_7',a_2_1_orders_2('#skF_6',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190561,c_188904])).

tff(c_182107,plain,(
    r2_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_261244,plain,(
    ! [D_95145,B_95146,C_95147] :
      ( r2_hidden('#skF_4'(D_95145,B_95146,C_95147,D_95145),C_95147)
      | r2_hidden(D_95145,a_2_1_orders_2(B_95146,C_95147))
      | ~ m1_subset_1(D_95145,u1_struct_0(B_95146))
      | ~ m1_subset_1(C_95147,k1_zfmisc_1(u1_struct_0(B_95146)))
      | ~ l1_orders_2(B_95146)
      | ~ v5_orders_2(B_95146)
      | ~ v4_orders_2(B_95146)
      | ~ v3_orders_2(B_95146)
      | v2_struct_0(B_95146) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_261472,plain,(
    ! [D_95145] :
      ( r2_hidden('#skF_4'(D_95145,'#skF_6',k1_tarski('#skF_8'),D_95145),k1_tarski('#skF_8'))
      | r2_hidden(D_95145,a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')))
      | ~ m1_subset_1(D_95145,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_188962,c_261244])).

tff(c_261481,plain,(
    ! [D_95145] :
      ( r2_hidden('#skF_4'(D_95145,'#skF_6',k1_tarski('#skF_8'),D_95145),k1_tarski('#skF_8'))
      | r2_hidden(D_95145,a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')))
      | ~ m1_subset_1(D_95145,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_261472])).

tff(c_261488,plain,(
    ! [D_95391] :
      ( r2_hidden('#skF_4'(D_95391,'#skF_6',k1_tarski('#skF_8'),D_95391),k1_tarski('#skF_8'))
      | r2_hidden(D_95391,a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')))
      | ~ m1_subset_1(D_95391,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_261481])).

tff(c_182115,plain,(
    ! [D_60463,B_60464,A_60465] :
      ( D_60463 = B_60464
      | D_60463 = A_60465
      | ~ r2_hidden(D_60463,k2_tarski(A_60465,B_60464)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_182124,plain,(
    ! [D_60463,A_7] :
      ( D_60463 = A_7
      | D_60463 = A_7
      | ~ r2_hidden(D_60463,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_182115])).

tff(c_262917,plain,(
    ! [D_95635] :
      ( '#skF_4'(D_95635,'#skF_6',k1_tarski('#skF_8'),D_95635) = '#skF_8'
      | r2_hidden(D_95635,a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')))
      | ~ m1_subset_1(D_95635,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_261488,c_182124])).

tff(c_262945,plain,
    ( '#skF_4'('#skF_7','#skF_6',k1_tarski('#skF_8'),'#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_262917,c_190567])).

tff(c_264377,plain,(
    '#skF_4'('#skF_7','#skF_6',k1_tarski('#skF_8'),'#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_262945])).

tff(c_277602,plain,(
    ! [B_99053,D_99054,C_99055] :
      ( ~ r2_orders_2(B_99053,D_99054,'#skF_4'(D_99054,B_99053,C_99055,D_99054))
      | r2_hidden(D_99054,a_2_1_orders_2(B_99053,C_99055))
      | ~ m1_subset_1(D_99054,u1_struct_0(B_99053))
      | ~ m1_subset_1(C_99055,k1_zfmisc_1(u1_struct_0(B_99053)))
      | ~ l1_orders_2(B_99053)
      | ~ v5_orders_2(B_99053)
      | ~ v4_orders_2(B_99053)
      | ~ v3_orders_2(B_99053)
      | v2_struct_0(B_99053) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_277614,plain,
    ( ~ r2_orders_2('#skF_6','#skF_7','#skF_8')
    | r2_hidden('#skF_7',a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_264377,c_277602])).

tff(c_277744,plain,
    ( r2_hidden('#skF_7',a_2_1_orders_2('#skF_6',k1_tarski('#skF_8')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_188962,c_66,c_182107,c_277614])).

tff(c_277746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_190567,c_277744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:18:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.52/24.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.60/24.78  
% 38.60/24.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.60/24.78  %$ r2_orders_2 > r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 38.60/24.78  
% 38.60/24.78  %Foreground sorts:
% 38.60/24.78  
% 38.60/24.78  
% 38.60/24.78  %Background operators:
% 38.60/24.78  
% 38.60/24.78  
% 38.60/24.78  %Foreground operators:
% 38.60/24.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 38.60/24.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 38.60/24.78  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 38.60/24.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.60/24.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.60/24.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 38.60/24.78  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 38.60/24.78  tff('#skF_7', type, '#skF_7': $i).
% 38.60/24.78  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 38.60/24.78  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 38.60/24.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 38.60/24.78  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 38.60/24.78  tff('#skF_6', type, '#skF_6': $i).
% 38.60/24.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 38.60/24.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 38.60/24.78  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 38.60/24.78  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 38.60/24.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 38.60/24.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 38.60/24.78  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 38.60/24.78  tff('#skF_8', type, '#skF_8': $i).
% 38.60/24.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.60/24.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 38.60/24.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.60/24.78  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 38.60/24.78  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 38.60/24.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 38.60/24.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 38.60/24.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 38.60/24.78  
% 38.60/24.80  tff(f_182, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_orders_2)).
% 38.60/24.80  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 38.60/24.80  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 38.60/24.80  tff(f_160, axiom, (![A]: ((v3_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~(((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) & ~r1_orders_2(A, B, C)) & ~r1_orders_2(A, C, B)) & ~((r1_orders_2(A, B, C) | r1_orders_2(A, C, B)) & (![D]: ((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~(r2_hidden(B, D) & r2_hidden(C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_orders_2)).
% 38.60/24.80  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 38.60/24.80  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 38.60/24.80  tff(f_59, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 38.60/24.80  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 38.60/24.80  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 38.60/24.80  tff(f_86, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 38.60/24.80  tff(c_76, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_74, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_72, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_70, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_68, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_64, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_66, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_182136, plain, (![A_60471, B_60472]: (k6_domain_1(A_60471, B_60472)=k1_tarski(B_60472) | ~m1_subset_1(B_60472, A_60471) | v1_xboole_0(A_60471))), inference(cnfTransformation, [status(thm)], [f_93])).
% 38.60/24.80  tff(c_182143, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_182136])).
% 38.60/24.80  tff(c_182145, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_182143])).
% 38.60/24.80  tff(c_182147, plain, (![A_60473, B_60474]: (r1_orders_2(A_60473, B_60474, B_60474) | ~m1_subset_1(B_60474, u1_struct_0(A_60473)) | ~l1_orders_2(A_60473) | ~v3_orders_2(A_60473) | v2_struct_0(A_60473))), inference(cnfTransformation, [status(thm)], [f_105])).
% 38.60/24.80  tff(c_182151, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_182147])).
% 38.60/24.80  tff(c_182158, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_182151])).
% 38.60/24.80  tff(c_182159, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_76, c_182158])).
% 38.60/24.80  tff(c_50, plain, (![A_35, B_47, C_53]: (~r1_orders_2(A_35, B_47, C_53) | r2_hidden(C_53, '#skF_5'(A_35, B_47, C_53)) | ~m1_subset_1(C_53, u1_struct_0(A_35)) | ~m1_subset_1(B_47, u1_struct_0(A_35)) | ~l1_orders_2(A_35) | ~v3_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_160])).
% 38.60/24.80  tff(c_184923, plain, (![A_64759, B_64760, C_64761]: (~r1_orders_2(A_64759, B_64760, C_64761) | m1_subset_1('#skF_5'(A_64759, B_64760, C_64761), k1_zfmisc_1(u1_struct_0(A_64759))) | ~m1_subset_1(C_64761, u1_struct_0(A_64759)) | ~m1_subset_1(B_64760, u1_struct_0(A_64759)) | ~l1_orders_2(A_64759) | ~v3_orders_2(A_64759))), inference(cnfTransformation, [status(thm)], [f_160])).
% 38.60/24.80  tff(c_22, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 38.60/24.80  tff(c_188863, plain, (![A_67185, A_67186, B_67187, C_67188]: (~v1_xboole_0(u1_struct_0(A_67185)) | ~r2_hidden(A_67186, '#skF_5'(A_67185, B_67187, C_67188)) | ~r1_orders_2(A_67185, B_67187, C_67188) | ~m1_subset_1(C_67188, u1_struct_0(A_67185)) | ~m1_subset_1(B_67187, u1_struct_0(A_67185)) | ~l1_orders_2(A_67185) | ~v3_orders_2(A_67185))), inference(resolution, [status(thm)], [c_184923, c_22])).
% 38.60/24.80  tff(c_188893, plain, (![A_67270, B_67271, C_67272]: (~v1_xboole_0(u1_struct_0(A_67270)) | ~r1_orders_2(A_67270, B_67271, C_67272) | ~m1_subset_1(C_67272, u1_struct_0(A_67270)) | ~m1_subset_1(B_67271, u1_struct_0(A_67270)) | ~l1_orders_2(A_67270) | ~v3_orders_2(A_67270))), inference(resolution, [status(thm)], [c_50, c_188863])).
% 38.60/24.80  tff(c_188895, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_182159, c_188893])).
% 38.60/24.80  tff(c_188901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_182145, c_188895])).
% 38.60/24.80  tff(c_188902, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_182143])).
% 38.60/24.80  tff(c_188943, plain, (![A_67367, B_67368]: (m1_subset_1(k6_domain_1(u1_struct_0(A_67367), B_67368), k1_zfmisc_1(u1_struct_0(A_67367))) | ~m1_subset_1(B_67368, u1_struct_0(A_67367)) | ~l1_orders_2(A_67367) | ~v3_orders_2(A_67367) | v2_struct_0(A_67367))), inference(cnfTransformation, [status(thm)], [f_119])).
% 38.60/24.80  tff(c_188954, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_188902, c_188943])).
% 38.60/24.80  tff(c_188961, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_64, c_188954])).
% 38.60/24.80  tff(c_188962, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_188961])).
% 38.60/24.80  tff(c_190542, plain, (![A_71439, B_71440]: (k2_orders_2(A_71439, B_71440)=a_2_1_orders_2(A_71439, B_71440) | ~m1_subset_1(B_71440, k1_zfmisc_1(u1_struct_0(A_71439))) | ~l1_orders_2(A_71439) | ~v5_orders_2(A_71439) | ~v4_orders_2(A_71439) | ~v3_orders_2(A_71439) | v2_struct_0(A_71439))), inference(cnfTransformation, [status(thm)], [f_59])).
% 38.60/24.80  tff(c_190551, plain, (k2_orders_2('#skF_6', k1_tarski('#skF_8'))=a_2_1_orders_2('#skF_6', k1_tarski('#skF_8')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_188962, c_190542])).
% 38.60/24.80  tff(c_190560, plain, (k2_orders_2('#skF_6', k1_tarski('#skF_8'))=a_2_1_orders_2('#skF_6', k1_tarski('#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_190551])).
% 38.60/24.80  tff(c_190561, plain, (k2_orders_2('#skF_6', k1_tarski('#skF_8'))=a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76, c_190560])).
% 38.60/24.80  tff(c_78, plain, (~r2_hidden('#skF_7', k2_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_8'))) | ~r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_98, plain, (~r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 38.60/24.80  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 38.60/24.80  tff(c_94, plain, (![D_62, B_63]: (r2_hidden(D_62, k2_tarski(D_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 38.60/24.80  tff(c_97, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 38.60/24.80  tff(c_126, plain, (![A_75, B_76]: (k6_domain_1(A_75, B_76)=k1_tarski(B_76) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_93])).
% 38.60/24.80  tff(c_133, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_126])).
% 38.60/24.80  tff(c_135, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_133])).
% 38.60/24.80  tff(c_138, plain, (![A_77, B_78]: (r1_orders_2(A_77, B_78, B_78) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_105])).
% 38.60/24.80  tff(c_142, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_138])).
% 38.60/24.80  tff(c_149, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_142])).
% 38.60/24.80  tff(c_150, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_76, c_149])).
% 38.60/24.80  tff(c_4676, plain, (![A_5990, B_5991, C_5992]: (~r1_orders_2(A_5990, B_5991, C_5992) | m1_subset_1('#skF_5'(A_5990, B_5991, C_5992), k1_zfmisc_1(u1_struct_0(A_5990))) | ~m1_subset_1(C_5992, u1_struct_0(A_5990)) | ~m1_subset_1(B_5991, u1_struct_0(A_5990)) | ~l1_orders_2(A_5990) | ~v3_orders_2(A_5990))), inference(cnfTransformation, [status(thm)], [f_160])).
% 38.60/24.80  tff(c_85013, plain, (![A_26890, A_26891, B_26892, C_26893]: (~v1_xboole_0(u1_struct_0(A_26890)) | ~r2_hidden(A_26891, '#skF_5'(A_26890, B_26892, C_26893)) | ~r1_orders_2(A_26890, B_26892, C_26893) | ~m1_subset_1(C_26893, u1_struct_0(A_26890)) | ~m1_subset_1(B_26892, u1_struct_0(A_26890)) | ~l1_orders_2(A_26890) | ~v3_orders_2(A_26890))), inference(resolution, [status(thm)], [c_4676, c_22])).
% 38.60/24.80  tff(c_85061, plain, (![A_27137, B_27138, C_27139]: (~v1_xboole_0(u1_struct_0(A_27137)) | ~r1_orders_2(A_27137, B_27138, C_27139) | ~m1_subset_1(C_27139, u1_struct_0(A_27137)) | ~m1_subset_1(B_27138, u1_struct_0(A_27137)) | ~l1_orders_2(A_27137) | ~v3_orders_2(A_27137))), inference(resolution, [status(thm)], [c_50, c_85013])).
% 38.60/24.80  tff(c_85063, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_150, c_85061])).
% 38.60/24.80  tff(c_85069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_135, c_85063])).
% 38.60/24.80  tff(c_85070, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_133])).
% 38.60/24.80  tff(c_85112, plain, (![A_27396, B_27397]: (m1_subset_1(k6_domain_1(u1_struct_0(A_27396), B_27397), k1_zfmisc_1(u1_struct_0(A_27396))) | ~m1_subset_1(B_27397, u1_struct_0(A_27396)) | ~l1_orders_2(A_27396) | ~v3_orders_2(A_27396) | v2_struct_0(A_27396))), inference(cnfTransformation, [status(thm)], [f_119])).
% 38.60/24.80  tff(c_85123, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_85070, c_85112])).
% 38.60/24.80  tff(c_85130, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_64, c_85123])).
% 38.60/24.80  tff(c_85131, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_85130])).
% 38.60/24.80  tff(c_86615, plain, (![A_31219, B_31220]: (k2_orders_2(A_31219, B_31220)=a_2_1_orders_2(A_31219, B_31220) | ~m1_subset_1(B_31220, k1_zfmisc_1(u1_struct_0(A_31219))) | ~l1_orders_2(A_31219) | ~v5_orders_2(A_31219) | ~v4_orders_2(A_31219) | ~v3_orders_2(A_31219) | v2_struct_0(A_31219))), inference(cnfTransformation, [status(thm)], [f_59])).
% 38.60/24.80  tff(c_86624, plain, (k2_orders_2('#skF_6', k1_tarski('#skF_8'))=a_2_1_orders_2('#skF_6', k1_tarski('#skF_8')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_85131, c_86615])).
% 38.60/24.80  tff(c_86633, plain, (k2_orders_2('#skF_6', k1_tarski('#skF_8'))=a_2_1_orders_2('#skF_6', k1_tarski('#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_86624])).
% 38.60/24.80  tff(c_86634, plain, (k2_orders_2('#skF_6', k1_tarski('#skF_8'))=a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76, c_86633])).
% 38.60/24.80  tff(c_84, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8') | r2_hidden('#skF_7', k2_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 38.60/24.80  tff(c_85076, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8') | r2_hidden('#skF_7', k2_orders_2('#skF_6', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_85070, c_84])).
% 38.60/24.80  tff(c_85077, plain, (r2_hidden('#skF_7', k2_orders_2('#skF_6', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_98, c_85076])).
% 38.60/24.80  tff(c_86640, plain, (r2_hidden('#skF_7', a_2_1_orders_2('#skF_6', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_86634, c_85077])).
% 38.60/24.80  tff(c_91997, plain, (![A_35290, B_35291, C_35292]: ('#skF_3'(A_35290, B_35291, C_35292)=A_35290 | ~r2_hidden(A_35290, a_2_1_orders_2(B_35291, C_35292)) | ~m1_subset_1(C_35292, k1_zfmisc_1(u1_struct_0(B_35291))) | ~l1_orders_2(B_35291) | ~v5_orders_2(B_35291) | ~v4_orders_2(B_35291) | ~v3_orders_2(B_35291) | v2_struct_0(B_35291))), inference(cnfTransformation, [status(thm)], [f_86])).
% 38.60/24.80  tff(c_92004, plain, ('#skF_3'('#skF_7', '#skF_6', k1_tarski('#skF_8'))='#skF_7' | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_86640, c_91997])).
% 38.60/24.80  tff(c_92018, plain, ('#skF_3'('#skF_7', '#skF_6', k1_tarski('#skF_8'))='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_85131, c_92004])).
% 38.60/24.80  tff(c_92019, plain, ('#skF_3'('#skF_7', '#skF_6', k1_tarski('#skF_8'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_76, c_92018])).
% 38.60/24.80  tff(c_180845, plain, (![B_59724, A_59725, C_59726, E_59727]: (r2_orders_2(B_59724, '#skF_3'(A_59725, B_59724, C_59726), E_59727) | ~r2_hidden(E_59727, C_59726) | ~m1_subset_1(E_59727, u1_struct_0(B_59724)) | ~r2_hidden(A_59725, a_2_1_orders_2(B_59724, C_59726)) | ~m1_subset_1(C_59726, k1_zfmisc_1(u1_struct_0(B_59724))) | ~l1_orders_2(B_59724) | ~v5_orders_2(B_59724) | ~v4_orders_2(B_59724) | ~v3_orders_2(B_59724) | v2_struct_0(B_59724))), inference(cnfTransformation, [status(thm)], [f_86])).
% 38.60/24.80  tff(c_180983, plain, (![A_59725, E_59727]: (r2_orders_2('#skF_6', '#skF_3'(A_59725, '#skF_6', k1_tarski('#skF_8')), E_59727) | ~r2_hidden(E_59727, k1_tarski('#skF_8')) | ~m1_subset_1(E_59727, u1_struct_0('#skF_6')) | ~r2_hidden(A_59725, a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_85131, c_180845])).
% 38.60/24.80  tff(c_180992, plain, (![A_59725, E_59727]: (r2_orders_2('#skF_6', '#skF_3'(A_59725, '#skF_6', k1_tarski('#skF_8')), E_59727) | ~r2_hidden(E_59727, k1_tarski('#skF_8')) | ~m1_subset_1(E_59727, u1_struct_0('#skF_6')) | ~r2_hidden(A_59725, a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_180983])).
% 38.60/24.80  tff(c_180999, plain, (![A_59971, E_59972]: (r2_orders_2('#skF_6', '#skF_3'(A_59971, '#skF_6', k1_tarski('#skF_8')), E_59972) | ~r2_hidden(E_59972, k1_tarski('#skF_8')) | ~m1_subset_1(E_59972, u1_struct_0('#skF_6')) | ~r2_hidden(A_59971, a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_180992])).
% 38.60/24.80  tff(c_181830, plain, (![E_59972]: (r2_orders_2('#skF_6', '#skF_7', E_59972) | ~r2_hidden(E_59972, k1_tarski('#skF_8')) | ~m1_subset_1(E_59972, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_7', a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_92019, c_180999])).
% 38.60/24.80  tff(c_181874, plain, (![E_60216]: (r2_orders_2('#skF_6', '#skF_7', E_60216) | ~r2_hidden(E_60216, k1_tarski('#skF_8')) | ~m1_subset_1(E_60216, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_86640, c_181830])).
% 38.60/24.80  tff(c_182097, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_97, c_181874])).
% 38.60/24.80  tff(c_182103, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_182097])).
% 38.60/24.80  tff(c_182105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_182103])).
% 38.60/24.80  tff(c_182106, plain, (~r2_hidden('#skF_7', k2_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_8')))), inference(splitRight, [status(thm)], [c_78])).
% 38.60/24.80  tff(c_188904, plain, (~r2_hidden('#skF_7', k2_orders_2('#skF_6', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_188902, c_182106])).
% 38.60/24.80  tff(c_190567, plain, (~r2_hidden('#skF_7', a_2_1_orders_2('#skF_6', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_190561, c_188904])).
% 38.60/24.80  tff(c_182107, plain, (r2_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 38.60/24.80  tff(c_261244, plain, (![D_95145, B_95146, C_95147]: (r2_hidden('#skF_4'(D_95145, B_95146, C_95147, D_95145), C_95147) | r2_hidden(D_95145, a_2_1_orders_2(B_95146, C_95147)) | ~m1_subset_1(D_95145, u1_struct_0(B_95146)) | ~m1_subset_1(C_95147, k1_zfmisc_1(u1_struct_0(B_95146))) | ~l1_orders_2(B_95146) | ~v5_orders_2(B_95146) | ~v4_orders_2(B_95146) | ~v3_orders_2(B_95146) | v2_struct_0(B_95146))), inference(cnfTransformation, [status(thm)], [f_86])).
% 38.60/24.80  tff(c_261472, plain, (![D_95145]: (r2_hidden('#skF_4'(D_95145, '#skF_6', k1_tarski('#skF_8'), D_95145), k1_tarski('#skF_8')) | r2_hidden(D_95145, a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))) | ~m1_subset_1(D_95145, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_188962, c_261244])).
% 38.60/24.80  tff(c_261481, plain, (![D_95145]: (r2_hidden('#skF_4'(D_95145, '#skF_6', k1_tarski('#skF_8'), D_95145), k1_tarski('#skF_8')) | r2_hidden(D_95145, a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))) | ~m1_subset_1(D_95145, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_261472])).
% 38.60/24.80  tff(c_261488, plain, (![D_95391]: (r2_hidden('#skF_4'(D_95391, '#skF_6', k1_tarski('#skF_8'), D_95391), k1_tarski('#skF_8')) | r2_hidden(D_95391, a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))) | ~m1_subset_1(D_95391, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_261481])).
% 38.60/24.80  tff(c_182115, plain, (![D_60463, B_60464, A_60465]: (D_60463=B_60464 | D_60463=A_60465 | ~r2_hidden(D_60463, k2_tarski(A_60465, B_60464)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 38.60/24.80  tff(c_182124, plain, (![D_60463, A_7]: (D_60463=A_7 | D_60463=A_7 | ~r2_hidden(D_60463, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_182115])).
% 38.60/24.80  tff(c_262917, plain, (![D_95635]: ('#skF_4'(D_95635, '#skF_6', k1_tarski('#skF_8'), D_95635)='#skF_8' | r2_hidden(D_95635, a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))) | ~m1_subset_1(D_95635, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_261488, c_182124])).
% 38.60/24.80  tff(c_262945, plain, ('#skF_4'('#skF_7', '#skF_6', k1_tarski('#skF_8'), '#skF_7')='#skF_8' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_262917, c_190567])).
% 38.60/24.80  tff(c_264377, plain, ('#skF_4'('#skF_7', '#skF_6', k1_tarski('#skF_8'), '#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_262945])).
% 38.60/24.80  tff(c_277602, plain, (![B_99053, D_99054, C_99055]: (~r2_orders_2(B_99053, D_99054, '#skF_4'(D_99054, B_99053, C_99055, D_99054)) | r2_hidden(D_99054, a_2_1_orders_2(B_99053, C_99055)) | ~m1_subset_1(D_99054, u1_struct_0(B_99053)) | ~m1_subset_1(C_99055, k1_zfmisc_1(u1_struct_0(B_99053))) | ~l1_orders_2(B_99053) | ~v5_orders_2(B_99053) | ~v4_orders_2(B_99053) | ~v3_orders_2(B_99053) | v2_struct_0(B_99053))), inference(cnfTransformation, [status(thm)], [f_86])).
% 38.60/24.80  tff(c_277614, plain, (~r2_orders_2('#skF_6', '#skF_7', '#skF_8') | r2_hidden('#skF_7', a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_264377, c_277602])).
% 38.60/24.80  tff(c_277744, plain, (r2_hidden('#skF_7', a_2_1_orders_2('#skF_6', k1_tarski('#skF_8'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_188962, c_66, c_182107, c_277614])).
% 38.60/24.80  tff(c_277746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_190567, c_277744])).
% 38.60/24.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.60/24.80  
% 38.60/24.80  Inference rules
% 38.60/24.80  ----------------------
% 38.60/24.80  #Ref     : 0
% 38.60/24.80  #Sup     : 30005
% 38.60/24.80  #Fact    : 184
% 38.60/24.80  #Define  : 0
% 38.60/24.80  #Split   : 33
% 38.60/24.80  #Chain   : 0
% 38.60/24.80  #Close   : 0
% 38.60/24.80  
% 38.60/24.80  Ordering : KBO
% 38.60/24.80  
% 38.60/24.80  Simplification rules
% 38.60/24.80  ----------------------
% 38.60/24.80  #Subsume      : 2557
% 38.60/24.80  #Demod        : 2149
% 38.60/24.80  #Tautology    : 1786
% 38.60/24.80  #SimpNegUnit  : 82
% 38.60/24.80  #BackRed      : 3
% 38.60/24.80  
% 38.60/24.80  #Partial instantiations: 54675
% 38.60/24.80  #Strategies tried      : 1
% 38.60/24.80  
% 38.60/24.80  Timing (in seconds)
% 38.60/24.80  ----------------------
% 38.60/24.80  Preprocessing        : 0.39
% 38.60/24.80  Parsing              : 0.20
% 38.60/24.80  CNF conversion       : 0.03
% 38.60/24.80  Main loop            : 23.58
% 38.60/24.80  Inferencing          : 6.68
% 38.60/24.80  Reduction            : 3.68
% 38.60/24.80  Demodulation         : 2.62
% 38.60/24.80  BG Simplification    : 1.18
% 38.60/24.80  Subsumption          : 11.31
% 38.60/24.80  Abstraction          : 1.84
% 38.60/24.80  MUC search           : 0.00
% 38.60/24.80  Cooper               : 0.00
% 38.60/24.80  Total                : 24.01
% 38.60/24.80  Index Insertion      : 0.00
% 38.60/24.80  Index Deletion       : 0.00
% 38.60/24.80  Index Matching       : 0.00
% 38.60/24.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
