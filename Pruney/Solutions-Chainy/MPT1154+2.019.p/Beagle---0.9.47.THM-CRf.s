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
% DateTime   : Thu Dec  3 10:19:35 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.17s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 151 expanded)
%              Number of leaves         :   30 (  72 expanded)
%              Depth                    :    8
%              Number of atoms          :  152 ( 505 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ! [A_15,B_17] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_15),B_17),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_17,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2469,plain,(
    ! [B_1976,A_1977,C_1978] :
      ( ~ r2_hidden(B_1976,k1_orders_2(A_1977,C_1978))
      | ~ r2_hidden(B_1976,C_1978)
      | ~ m1_subset_1(C_1978,k1_zfmisc_1(u1_struct_0(A_1977)))
      | ~ m1_subset_1(B_1976,u1_struct_0(A_1977))
      | ~ l1_orders_2(A_1977)
      | ~ v5_orders_2(A_1977)
      | ~ v4_orders_2(A_1977)
      | ~ v3_orders_2(A_1977)
      | v2_struct_0(A_1977) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2477,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2469])).

tff(c_2481,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_2477])).

tff(c_2482,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2481])).

tff(c_2483,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2482])).

tff(c_2494,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2483])).

tff(c_2497,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_2494])).

tff(c_2499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2497])).

tff(c_2501,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2482])).

tff(c_87,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_93,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_1897,plain,(
    ! [A_1788,B_1789] :
      ( m1_subset_1(k1_orders_2(A_1788,B_1789),k1_zfmisc_1(u1_struct_0(A_1788)))
      | ~ m1_subset_1(B_1789,k1_zfmisc_1(u1_struct_0(A_1788)))
      | ~ l1_orders_2(A_1788)
      | ~ v5_orders_2(A_1788)
      | ~ v4_orders_2(A_1788)
      | ~ v3_orders_2(A_1788)
      | v2_struct_0(A_1788) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3544,plain,(
    ! [A_2863,A_2864,B_2865] :
      ( ~ v1_xboole_0(u1_struct_0(A_2863))
      | ~ r2_hidden(A_2864,k1_orders_2(A_2863,B_2865))
      | ~ m1_subset_1(B_2865,k1_zfmisc_1(u1_struct_0(A_2863)))
      | ~ l1_orders_2(A_2863)
      | ~ v5_orders_2(A_2863)
      | ~ v4_orders_2(A_2863)
      | ~ v3_orders_2(A_2863)
      | v2_struct_0(A_2863) ) ),
    inference(resolution,[status(thm)],[c_1897,c_22])).

tff(c_3557,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_3544])).

tff(c_3566,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_2501,c_93,c_3557])).

tff(c_3568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3566])).

tff(c_3569,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_3585,plain,(
    ! [A_2919,B_2920] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_2919),B_2920),k1_zfmisc_1(u1_struct_0(A_2919)))
      | ~ m1_subset_1(B_2920,u1_struct_0(A_2919))
      | ~ l1_orders_2(A_2919)
      | ~ v3_orders_2(A_2919)
      | v2_struct_0(A_2919) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3593,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3569,c_3585])).

tff(c_3597,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_3593])).

tff(c_3598,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3597])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [D_27,A_28] : r2_hidden(D_27,k2_tarski(A_28,D_27)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_3571,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3569,c_34])).

tff(c_5872,plain,(
    ! [B_5029,A_5030,C_5031] :
      ( ~ r2_hidden(B_5029,k1_orders_2(A_5030,C_5031))
      | ~ r2_hidden(B_5029,C_5031)
      | ~ m1_subset_1(C_5031,k1_zfmisc_1(u1_struct_0(A_5030)))
      | ~ m1_subset_1(B_5029,u1_struct_0(A_5030))
      | ~ l1_orders_2(A_5030)
      | ~ v5_orders_2(A_5030)
      | ~ v4_orders_2(A_5030)
      | ~ v3_orders_2(A_5030)
      | v2_struct_0(A_5030) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5880,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3571,c_5872])).

tff(c_5884,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_3598,c_59,c_5880])).

tff(c_5886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.28  
% 6.17/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.28  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 6.17/2.28  
% 6.17/2.28  %Foreground sorts:
% 6.17/2.28  
% 6.17/2.28  
% 6.17/2.28  %Background operators:
% 6.17/2.28  
% 6.17/2.28  
% 6.17/2.28  %Foreground operators:
% 6.17/2.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.17/2.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.17/2.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.17/2.28  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 6.17/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.17/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.17/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.17/2.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.17/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.17/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.17/2.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.17/2.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.17/2.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.17/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.17/2.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.17/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.17/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.17/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.17/2.28  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 6.17/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.17/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.17/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.17/2.28  
% 6.17/2.29  tff(f_119, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 6.17/2.29  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 6.17/2.29  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 6.17/2.29  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.17/2.29  tff(f_58, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 6.17/2.29  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.17/2.29  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.17/2.29  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.17/2.29  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.17/2.29  tff(c_44, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.17/2.29  tff(c_42, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.17/2.29  tff(c_40, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.17/2.29  tff(c_38, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.17/2.29  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.17/2.29  tff(c_28, plain, (![A_15, B_17]: (m1_subset_1(k6_domain_1(u1_struct_0(A_15), B_17), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_17, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.17/2.29  tff(c_34, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.17/2.29  tff(c_2469, plain, (![B_1976, A_1977, C_1978]: (~r2_hidden(B_1976, k1_orders_2(A_1977, C_1978)) | ~r2_hidden(B_1976, C_1978) | ~m1_subset_1(C_1978, k1_zfmisc_1(u1_struct_0(A_1977))) | ~m1_subset_1(B_1976, u1_struct_0(A_1977)) | ~l1_orders_2(A_1977) | ~v5_orders_2(A_1977) | ~v4_orders_2(A_1977) | ~v3_orders_2(A_1977) | v2_struct_0(A_1977))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.17/2.29  tff(c_2477, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2469])).
% 6.17/2.29  tff(c_2481, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_2477])).
% 6.17/2.29  tff(c_2482, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_2481])).
% 6.17/2.29  tff(c_2483, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2482])).
% 6.17/2.29  tff(c_2494, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_2483])).
% 6.17/2.29  tff(c_2497, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_2494])).
% 6.17/2.29  tff(c_2499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_2497])).
% 6.17/2.29  tff(c_2501, plain, (m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2482])).
% 6.17/2.29  tff(c_87, plain, (![A_40, B_41]: (k6_domain_1(A_40, B_41)=k1_tarski(B_41) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.17/2.29  tff(c_91, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_87])).
% 6.17/2.29  tff(c_93, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_91])).
% 6.17/2.29  tff(c_1897, plain, (![A_1788, B_1789]: (m1_subset_1(k1_orders_2(A_1788, B_1789), k1_zfmisc_1(u1_struct_0(A_1788))) | ~m1_subset_1(B_1789, k1_zfmisc_1(u1_struct_0(A_1788))) | ~l1_orders_2(A_1788) | ~v5_orders_2(A_1788) | ~v4_orders_2(A_1788) | ~v3_orders_2(A_1788) | v2_struct_0(A_1788))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.17/2.29  tff(c_22, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.17/2.29  tff(c_3544, plain, (![A_2863, A_2864, B_2865]: (~v1_xboole_0(u1_struct_0(A_2863)) | ~r2_hidden(A_2864, k1_orders_2(A_2863, B_2865)) | ~m1_subset_1(B_2865, k1_zfmisc_1(u1_struct_0(A_2863))) | ~l1_orders_2(A_2863) | ~v5_orders_2(A_2863) | ~v4_orders_2(A_2863) | ~v3_orders_2(A_2863) | v2_struct_0(A_2863))), inference(resolution, [status(thm)], [c_1897, c_22])).
% 6.17/2.29  tff(c_3557, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_3544])).
% 6.17/2.29  tff(c_3566, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_2501, c_93, c_3557])).
% 6.17/2.29  tff(c_3568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_3566])).
% 6.17/2.29  tff(c_3569, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_91])).
% 6.17/2.29  tff(c_3585, plain, (![A_2919, B_2920]: (m1_subset_1(k6_domain_1(u1_struct_0(A_2919), B_2920), k1_zfmisc_1(u1_struct_0(A_2919))) | ~m1_subset_1(B_2920, u1_struct_0(A_2919)) | ~l1_orders_2(A_2919) | ~v3_orders_2(A_2919) | v2_struct_0(A_2919))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.17/2.29  tff(c_3593, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3569, c_3585])).
% 6.17/2.29  tff(c_3597, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_3593])).
% 6.17/2.29  tff(c_3598, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_3597])).
% 6.17/2.29  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.17/2.29  tff(c_56, plain, (![D_27, A_28]: (r2_hidden(D_27, k2_tarski(A_28, D_27)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.17/2.29  tff(c_59, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_56])).
% 6.17/2.29  tff(c_3571, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3569, c_34])).
% 6.17/2.29  tff(c_5872, plain, (![B_5029, A_5030, C_5031]: (~r2_hidden(B_5029, k1_orders_2(A_5030, C_5031)) | ~r2_hidden(B_5029, C_5031) | ~m1_subset_1(C_5031, k1_zfmisc_1(u1_struct_0(A_5030))) | ~m1_subset_1(B_5029, u1_struct_0(A_5030)) | ~l1_orders_2(A_5030) | ~v5_orders_2(A_5030) | ~v4_orders_2(A_5030) | ~v3_orders_2(A_5030) | v2_struct_0(A_5030))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.17/2.29  tff(c_5880, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3571, c_5872])).
% 6.17/2.29  tff(c_5884, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_3598, c_59, c_5880])).
% 6.17/2.29  tff(c_5886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_5884])).
% 6.17/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.29  
% 6.17/2.29  Inference rules
% 6.17/2.29  ----------------------
% 6.17/2.29  #Ref     : 0
% 6.17/2.29  #Sup     : 890
% 6.17/2.29  #Fact    : 36
% 6.17/2.29  #Define  : 0
% 6.17/2.29  #Split   : 7
% 6.17/2.29  #Chain   : 0
% 6.17/2.29  #Close   : 0
% 6.17/2.29  
% 6.17/2.29  Ordering : KBO
% 6.17/2.29  
% 6.17/2.29  Simplification rules
% 6.17/2.29  ----------------------
% 6.17/2.29  #Subsume      : 310
% 6.17/2.29  #Demod        : 137
% 6.17/2.29  #Tautology    : 273
% 6.17/2.29  #SimpNegUnit  : 8
% 6.17/2.29  #BackRed      : 1
% 6.17/2.29  
% 6.17/2.29  #Partial instantiations: 3240
% 6.17/2.29  #Strategies tried      : 1
% 6.17/2.29  
% 6.17/2.29  Timing (in seconds)
% 6.17/2.29  ----------------------
% 6.17/2.30  Preprocessing        : 0.31
% 6.17/2.30  Parsing              : 0.16
% 6.17/2.30  CNF conversion       : 0.02
% 6.17/2.30  Main loop            : 1.12
% 6.17/2.30  Inferencing          : 0.52
% 6.17/2.30  Reduction            : 0.26
% 6.17/2.30  Demodulation         : 0.19
% 6.17/2.30  BG Simplification    : 0.05
% 6.17/2.30  Subsumption          : 0.22
% 6.17/2.30  Abstraction          : 0.07
% 6.17/2.30  MUC search           : 0.00
% 6.17/2.30  Cooper               : 0.00
% 6.17/2.30  Total                : 1.46
% 6.17/2.30  Index Insertion      : 0.00
% 6.17/2.30  Index Deletion       : 0.00
% 6.17/2.30  Index Matching       : 0.00
% 6.17/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
