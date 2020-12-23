%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:39 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 151 expanded)
%              Number of leaves         :   31 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  152 ( 491 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_108,axiom,(
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
                  & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    ! [A_17,B_19] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_17),B_19),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_19,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v3_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1812,plain,(
    ! [B_1838,A_1839,C_1840] :
      ( ~ r2_hidden(B_1838,k2_orders_2(A_1839,C_1840))
      | ~ r2_hidden(B_1838,C_1840)
      | ~ m1_subset_1(C_1840,k1_zfmisc_1(u1_struct_0(A_1839)))
      | ~ m1_subset_1(B_1838,u1_struct_0(A_1839))
      | ~ l1_orders_2(A_1839)
      | ~ v5_orders_2(A_1839)
      | ~ v4_orders_2(A_1839)
      | ~ v3_orders_2(A_1839)
      | v2_struct_0(A_1839) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1820,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1812])).

tff(c_1824,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_1820])).

tff(c_1825,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1824])).

tff(c_1826,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1825])).

tff(c_1837,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1826])).

tff(c_1843,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_1837])).

tff(c_1845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1843])).

tff(c_1847,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1825])).

tff(c_89,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_102,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_1202,plain,(
    ! [A_1555,B_1556] :
      ( m1_subset_1(k2_orders_2(A_1555,B_1556),k1_zfmisc_1(u1_struct_0(A_1555)))
      | ~ m1_subset_1(B_1556,k1_zfmisc_1(u1_struct_0(A_1555)))
      | ~ l1_orders_2(A_1555)
      | ~ v5_orders_2(A_1555)
      | ~ v4_orders_2(A_1555)
      | ~ v3_orders_2(A_1555)
      | v2_struct_0(A_1555) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3815,plain,(
    ! [A_3007,A_3008,B_3009] :
      ( ~ v1_xboole_0(u1_struct_0(A_3007))
      | ~ r2_hidden(A_3008,k2_orders_2(A_3007,B_3009))
      | ~ m1_subset_1(B_3009,k1_zfmisc_1(u1_struct_0(A_3007)))
      | ~ l1_orders_2(A_3007)
      | ~ v5_orders_2(A_3007)
      | ~ v4_orders_2(A_3007)
      | ~ v3_orders_2(A_3007)
      | v2_struct_0(A_3007) ) ),
    inference(resolution,[status(thm)],[c_1202,c_22])).

tff(c_3828,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_3815])).

tff(c_3837,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1847,c_102,c_3828])).

tff(c_3839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3837])).

tff(c_3841,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_3840,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k6_domain_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3846,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3840,c_26])).

tff(c_3850,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3846])).

tff(c_3851,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3841,c_3850])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    ! [D_29,B_30] : r2_hidden(D_29,k2_tarski(D_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_61,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_3842,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3840,c_36])).

tff(c_6014,plain,(
    ! [B_5221,A_5222,C_5223] :
      ( ~ r2_hidden(B_5221,k2_orders_2(A_5222,C_5223))
      | ~ r2_hidden(B_5221,C_5223)
      | ~ m1_subset_1(C_5223,k1_zfmisc_1(u1_struct_0(A_5222)))
      | ~ m1_subset_1(B_5221,u1_struct_0(A_5222))
      | ~ l1_orders_2(A_5222)
      | ~ v5_orders_2(A_5222)
      | ~ v4_orders_2(A_5222)
      | ~ v3_orders_2(A_5222)
      | v2_struct_0(A_5222) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6022,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3842,c_6014])).

tff(c_6026,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_3851,c_61,c_6022])).

tff(c_6028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.08  
% 5.78/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.09  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.78/2.09  
% 5.78/2.09  %Foreground sorts:
% 5.78/2.09  
% 5.78/2.09  
% 5.78/2.09  %Background operators:
% 5.78/2.09  
% 5.78/2.09  
% 5.78/2.09  %Foreground operators:
% 5.78/2.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.78/2.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.78/2.09  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.78/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.78/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.78/2.09  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.78/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.78/2.09  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.78/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.78/2.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.78/2.09  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.78/2.09  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.78/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.78/2.09  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.78/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.78/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.09  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 5.78/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.78/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.78/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.78/2.09  
% 5.78/2.10  tff(f_126, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 5.78/2.10  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 5.78/2.10  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 5.78/2.10  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.78/2.10  tff(f_58, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 5.78/2.10  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.78/2.10  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.78/2.10  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.78/2.10  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 5.78/2.10  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.78/2.10  tff(c_46, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.78/2.10  tff(c_44, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.78/2.10  tff(c_42, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.78/2.10  tff(c_40, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.78/2.10  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.78/2.10  tff(c_30, plain, (![A_17, B_19]: (m1_subset_1(k6_domain_1(u1_struct_0(A_17), B_19), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_19, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v3_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.78/2.10  tff(c_36, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.78/2.10  tff(c_1812, plain, (![B_1838, A_1839, C_1840]: (~r2_hidden(B_1838, k2_orders_2(A_1839, C_1840)) | ~r2_hidden(B_1838, C_1840) | ~m1_subset_1(C_1840, k1_zfmisc_1(u1_struct_0(A_1839))) | ~m1_subset_1(B_1838, u1_struct_0(A_1839)) | ~l1_orders_2(A_1839) | ~v5_orders_2(A_1839) | ~v4_orders_2(A_1839) | ~v3_orders_2(A_1839) | v2_struct_0(A_1839))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.78/2.10  tff(c_1820, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1812])).
% 5.78/2.10  tff(c_1824, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_1820])).
% 5.78/2.10  tff(c_1825, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_1824])).
% 5.78/2.10  tff(c_1826, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1825])).
% 5.78/2.10  tff(c_1837, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1826])).
% 5.78/2.10  tff(c_1843, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_1837])).
% 5.78/2.10  tff(c_1845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1843])).
% 5.78/2.10  tff(c_1847, plain, (m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1825])).
% 5.78/2.10  tff(c_89, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.78/2.10  tff(c_93, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_89])).
% 5.78/2.10  tff(c_102, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_93])).
% 5.78/2.10  tff(c_1202, plain, (![A_1555, B_1556]: (m1_subset_1(k2_orders_2(A_1555, B_1556), k1_zfmisc_1(u1_struct_0(A_1555))) | ~m1_subset_1(B_1556, k1_zfmisc_1(u1_struct_0(A_1555))) | ~l1_orders_2(A_1555) | ~v5_orders_2(A_1555) | ~v4_orders_2(A_1555) | ~v3_orders_2(A_1555) | v2_struct_0(A_1555))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.78/2.10  tff(c_22, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.78/2.10  tff(c_3815, plain, (![A_3007, A_3008, B_3009]: (~v1_xboole_0(u1_struct_0(A_3007)) | ~r2_hidden(A_3008, k2_orders_2(A_3007, B_3009)) | ~m1_subset_1(B_3009, k1_zfmisc_1(u1_struct_0(A_3007))) | ~l1_orders_2(A_3007) | ~v5_orders_2(A_3007) | ~v4_orders_2(A_3007) | ~v3_orders_2(A_3007) | v2_struct_0(A_3007))), inference(resolution, [status(thm)], [c_1202, c_22])).
% 5.78/2.10  tff(c_3828, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_3815])).
% 5.78/2.10  tff(c_3837, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1847, c_102, c_3828])).
% 5.78/2.10  tff(c_3839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_3837])).
% 5.78/2.10  tff(c_3841, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_93])).
% 5.78/2.10  tff(c_3840, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_93])).
% 5.78/2.10  tff(c_26, plain, (![A_13, B_14]: (m1_subset_1(k6_domain_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.78/2.10  tff(c_3846, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3840, c_26])).
% 5.78/2.10  tff(c_3850, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3846])).
% 5.78/2.10  tff(c_3851, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_3841, c_3850])).
% 5.78/2.10  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.78/2.10  tff(c_58, plain, (![D_29, B_30]: (r2_hidden(D_29, k2_tarski(D_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.78/2.10  tff(c_61, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_58])).
% 5.78/2.10  tff(c_3842, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3840, c_36])).
% 5.78/2.10  tff(c_6014, plain, (![B_5221, A_5222, C_5223]: (~r2_hidden(B_5221, k2_orders_2(A_5222, C_5223)) | ~r2_hidden(B_5221, C_5223) | ~m1_subset_1(C_5223, k1_zfmisc_1(u1_struct_0(A_5222))) | ~m1_subset_1(B_5221, u1_struct_0(A_5222)) | ~l1_orders_2(A_5222) | ~v5_orders_2(A_5222) | ~v4_orders_2(A_5222) | ~v3_orders_2(A_5222) | v2_struct_0(A_5222))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.78/2.10  tff(c_6022, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3842, c_6014])).
% 5.78/2.10  tff(c_6026, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_3851, c_61, c_6022])).
% 5.78/2.10  tff(c_6028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_6026])).
% 5.78/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.10  
% 5.78/2.10  Inference rules
% 5.78/2.10  ----------------------
% 5.78/2.10  #Ref     : 0
% 5.78/2.10  #Sup     : 905
% 5.78/2.10  #Fact    : 36
% 5.78/2.10  #Define  : 0
% 5.78/2.10  #Split   : 7
% 5.78/2.10  #Chain   : 0
% 5.78/2.10  #Close   : 0
% 5.78/2.10  
% 5.78/2.10  Ordering : KBO
% 5.78/2.10  
% 5.78/2.10  Simplification rules
% 5.78/2.10  ----------------------
% 5.78/2.10  #Subsume      : 311
% 5.78/2.10  #Demod        : 142
% 5.78/2.10  #Tautology    : 277
% 5.78/2.10  #SimpNegUnit  : 10
% 5.78/2.10  #BackRed      : 1
% 5.78/2.10  
% 5.78/2.10  #Partial instantiations: 3360
% 5.78/2.10  #Strategies tried      : 1
% 5.78/2.10  
% 5.78/2.10  Timing (in seconds)
% 5.78/2.10  ----------------------
% 5.87/2.10  Preprocessing        : 0.32
% 5.87/2.10  Parsing              : 0.17
% 5.87/2.10  CNF conversion       : 0.02
% 5.87/2.10  Main loop            : 1.02
% 5.87/2.10  Inferencing          : 0.48
% 5.87/2.10  Reduction            : 0.21
% 5.87/2.10  Demodulation         : 0.15
% 5.87/2.10  BG Simplification    : 0.05
% 5.87/2.10  Subsumption          : 0.21
% 5.87/2.10  Abstraction          : 0.07
% 5.87/2.10  MUC search           : 0.00
% 5.87/2.10  Cooper               : 0.00
% 5.87/2.10  Total                : 1.37
% 5.87/2.10  Index Insertion      : 0.00
% 5.87/2.10  Index Deletion       : 0.00
% 5.87/2.10  Index Matching       : 0.00
% 5.87/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
