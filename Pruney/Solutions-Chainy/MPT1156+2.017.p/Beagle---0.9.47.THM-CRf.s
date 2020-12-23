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
% DateTime   : Thu Dec  3 10:19:39 EST 2020

% Result     : Theorem 6.01s
% Output     : CNFRefutation 6.01s
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

tff(f_125,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_107,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    ! [A_18,B_20] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_18),B_20),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_20,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18)
      | ~ v3_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1900,plain,(
    ! [B_1840,A_1841,C_1842] :
      ( ~ r2_hidden(B_1840,k2_orders_2(A_1841,C_1842))
      | ~ r2_hidden(B_1840,C_1842)
      | ~ m1_subset_1(C_1842,k1_zfmisc_1(u1_struct_0(A_1841)))
      | ~ m1_subset_1(B_1840,u1_struct_0(A_1841))
      | ~ l1_orders_2(A_1841)
      | ~ v5_orders_2(A_1841)
      | ~ v4_orders_2(A_1841)
      | ~ v3_orders_2(A_1841)
      | v2_struct_0(A_1841) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1908,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1900])).

tff(c_1912,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_1908])).

tff(c_1913,plain,
    ( ~ r2_hidden('#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1912])).

tff(c_1914,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1913])).

tff(c_1925,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1914])).

tff(c_1928,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_1925])).

tff(c_1930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1928])).

tff(c_1932,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1913])).

tff(c_90,plain,(
    ! [A_46,B_47] :
      ( k6_domain_1(A_46,B_47) = k1_tarski(B_47)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_95,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_1529,plain,(
    ! [A_1653,B_1654] :
      ( m1_subset_1(k2_orders_2(A_1653,B_1654),k1_zfmisc_1(u1_struct_0(A_1653)))
      | ~ m1_subset_1(B_1654,k1_zfmisc_1(u1_struct_0(A_1653)))
      | ~ l1_orders_2(A_1653)
      | ~ v5_orders_2(A_1653)
      | ~ v4_orders_2(A_1653)
      | ~ v3_orders_2(A_1653)
      | v2_struct_0(A_1653) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [C_13,B_12,A_11] :
      ( ~ v1_xboole_0(C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(C_13))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4665,plain,(
    ! [A_3106,A_3107,B_3108] :
      ( ~ v1_xboole_0(u1_struct_0(A_3106))
      | ~ r2_hidden(A_3107,k2_orders_2(A_3106,B_3108))
      | ~ m1_subset_1(B_3108,k1_zfmisc_1(u1_struct_0(A_3106)))
      | ~ l1_orders_2(A_3106)
      | ~ v5_orders_2(A_3106)
      | ~ v4_orders_2(A_3106)
      | ~ v3_orders_2(A_3106)
      | v2_struct_0(A_3106) ) ),
    inference(resolution,[status(thm)],[c_1529,c_24])).

tff(c_4676,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_4665])).

tff(c_4681,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1932,c_95,c_4676])).

tff(c_4683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4681])).

tff(c_4684,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_4701,plain,(
    ! [A_3165,B_3166] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_3165),B_3166),k1_zfmisc_1(u1_struct_0(A_3165)))
      | ~ m1_subset_1(B_3166,u1_struct_0(A_3165))
      | ~ l1_orders_2(A_3165)
      | ~ v3_orders_2(A_3165)
      | v2_struct_0(A_3165) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4711,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4684,c_4701])).

tff(c_4716,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_4711])).

tff(c_4717,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4716])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    ! [D_30,B_31] : r2_hidden(D_30,k2_tarski(D_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_61,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_4686,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4684,c_36])).

tff(c_6927,plain,(
    ! [B_5412,A_5413,C_5414] :
      ( ~ r2_hidden(B_5412,k2_orders_2(A_5413,C_5414))
      | ~ r2_hidden(B_5412,C_5414)
      | ~ m1_subset_1(C_5414,k1_zfmisc_1(u1_struct_0(A_5413)))
      | ~ m1_subset_1(B_5412,u1_struct_0(A_5413))
      | ~ l1_orders_2(A_5413)
      | ~ v5_orders_2(A_5413)
      | ~ v4_orders_2(A_5413)
      | ~ v3_orders_2(A_5413)
      | v2_struct_0(A_5413) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6935,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4686,c_6927])).

tff(c_6939,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_4717,c_61,c_6935])).

tff(c_6941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:48:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.01/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.17  
% 6.01/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.18  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 6.01/2.18  
% 6.01/2.18  %Foreground sorts:
% 6.01/2.18  
% 6.01/2.18  
% 6.01/2.18  %Background operators:
% 6.01/2.18  
% 6.01/2.18  
% 6.01/2.18  %Foreground operators:
% 6.01/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.01/2.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.01/2.18  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.01/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.01/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.01/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.01/2.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.01/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.01/2.18  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 6.01/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.01/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.01/2.18  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.01/2.18  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.01/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.01/2.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.01/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.01/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.01/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.01/2.18  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 6.01/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.01/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.01/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.01/2.18  
% 6.01/2.19  tff(f_125, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 6.01/2.19  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 6.01/2.19  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 6.01/2.19  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.01/2.19  tff(f_64, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 6.01/2.19  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.01/2.19  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.01/2.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.01/2.19  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.01/2.19  tff(c_46, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.01/2.19  tff(c_44, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.01/2.19  tff(c_42, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.01/2.19  tff(c_40, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.01/2.19  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.01/2.19  tff(c_30, plain, (![A_18, B_20]: (m1_subset_1(k6_domain_1(u1_struct_0(A_18), B_20), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_20, u1_struct_0(A_18)) | ~l1_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.01/2.19  tff(c_36, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.01/2.19  tff(c_1900, plain, (![B_1840, A_1841, C_1842]: (~r2_hidden(B_1840, k2_orders_2(A_1841, C_1842)) | ~r2_hidden(B_1840, C_1842) | ~m1_subset_1(C_1842, k1_zfmisc_1(u1_struct_0(A_1841))) | ~m1_subset_1(B_1840, u1_struct_0(A_1841)) | ~l1_orders_2(A_1841) | ~v5_orders_2(A_1841) | ~v4_orders_2(A_1841) | ~v3_orders_2(A_1841) | v2_struct_0(A_1841))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.01/2.19  tff(c_1908, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1900])).
% 6.01/2.19  tff(c_1912, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_1908])).
% 6.01/2.19  tff(c_1913, plain, (~r2_hidden('#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_1912])).
% 6.01/2.19  tff(c_1914, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1913])).
% 6.01/2.19  tff(c_1925, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1914])).
% 6.01/2.19  tff(c_1928, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_1925])).
% 6.01/2.19  tff(c_1930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1928])).
% 6.01/2.19  tff(c_1932, plain, (m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1913])).
% 6.01/2.19  tff(c_90, plain, (![A_46, B_47]: (k6_domain_1(A_46, B_47)=k1_tarski(B_47) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.01/2.19  tff(c_94, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_90])).
% 6.01/2.19  tff(c_95, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_94])).
% 6.01/2.19  tff(c_1529, plain, (![A_1653, B_1654]: (m1_subset_1(k2_orders_2(A_1653, B_1654), k1_zfmisc_1(u1_struct_0(A_1653))) | ~m1_subset_1(B_1654, k1_zfmisc_1(u1_struct_0(A_1653))) | ~l1_orders_2(A_1653) | ~v5_orders_2(A_1653) | ~v4_orders_2(A_1653) | ~v3_orders_2(A_1653) | v2_struct_0(A_1653))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.01/2.19  tff(c_24, plain, (![C_13, B_12, A_11]: (~v1_xboole_0(C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(C_13)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.01/2.19  tff(c_4665, plain, (![A_3106, A_3107, B_3108]: (~v1_xboole_0(u1_struct_0(A_3106)) | ~r2_hidden(A_3107, k2_orders_2(A_3106, B_3108)) | ~m1_subset_1(B_3108, k1_zfmisc_1(u1_struct_0(A_3106))) | ~l1_orders_2(A_3106) | ~v5_orders_2(A_3106) | ~v4_orders_2(A_3106) | ~v3_orders_2(A_3106) | v2_struct_0(A_3106))), inference(resolution, [status(thm)], [c_1529, c_24])).
% 6.01/2.19  tff(c_4676, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_4665])).
% 6.01/2.19  tff(c_4681, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1932, c_95, c_4676])).
% 6.01/2.19  tff(c_4683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_4681])).
% 6.01/2.19  tff(c_4684, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_94])).
% 6.01/2.19  tff(c_4701, plain, (![A_3165, B_3166]: (m1_subset_1(k6_domain_1(u1_struct_0(A_3165), B_3166), k1_zfmisc_1(u1_struct_0(A_3165))) | ~m1_subset_1(B_3166, u1_struct_0(A_3165)) | ~l1_orders_2(A_3165) | ~v3_orders_2(A_3165) | v2_struct_0(A_3165))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.01/2.19  tff(c_4711, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4684, c_4701])).
% 6.01/2.19  tff(c_4716, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_4711])).
% 6.01/2.19  tff(c_4717, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_4716])).
% 6.01/2.19  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.01/2.19  tff(c_58, plain, (![D_30, B_31]: (r2_hidden(D_30, k2_tarski(D_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.01/2.19  tff(c_61, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_58])).
% 6.01/2.19  tff(c_4686, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4684, c_36])).
% 6.01/2.19  tff(c_6927, plain, (![B_5412, A_5413, C_5414]: (~r2_hidden(B_5412, k2_orders_2(A_5413, C_5414)) | ~r2_hidden(B_5412, C_5414) | ~m1_subset_1(C_5414, k1_zfmisc_1(u1_struct_0(A_5413))) | ~m1_subset_1(B_5412, u1_struct_0(A_5413)) | ~l1_orders_2(A_5413) | ~v5_orders_2(A_5413) | ~v4_orders_2(A_5413) | ~v3_orders_2(A_5413) | v2_struct_0(A_5413))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.01/2.19  tff(c_6935, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_4686, c_6927])).
% 6.01/2.19  tff(c_6939, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_4717, c_61, c_6935])).
% 6.01/2.19  tff(c_6941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_6939])).
% 6.01/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.19  
% 6.01/2.19  Inference rules
% 6.01/2.19  ----------------------
% 6.01/2.19  #Ref     : 0
% 6.01/2.19  #Sup     : 1067
% 6.01/2.19  #Fact    : 42
% 6.01/2.19  #Define  : 0
% 6.01/2.19  #Split   : 7
% 6.01/2.19  #Chain   : 0
% 6.01/2.19  #Close   : 0
% 6.01/2.19  
% 6.01/2.19  Ordering : KBO
% 6.01/2.19  
% 6.01/2.19  Simplification rules
% 6.01/2.19  ----------------------
% 6.01/2.19  #Subsume      : 393
% 6.01/2.19  #Demod        : 152
% 6.01/2.19  #Tautology    : 339
% 6.01/2.19  #SimpNegUnit  : 9
% 6.01/2.19  #BackRed      : 1
% 6.01/2.19  
% 6.01/2.19  #Partial instantiations: 3480
% 6.01/2.19  #Strategies tried      : 1
% 6.01/2.19  
% 6.01/2.19  Timing (in seconds)
% 6.01/2.19  ----------------------
% 6.01/2.19  Preprocessing        : 0.32
% 6.01/2.19  Parsing              : 0.17
% 6.01/2.19  CNF conversion       : 0.02
% 6.01/2.19  Main loop            : 1.12
% 6.01/2.19  Inferencing          : 0.53
% 6.01/2.19  Reduction            : 0.23
% 6.01/2.19  Demodulation         : 0.16
% 6.01/2.19  BG Simplification    : 0.05
% 6.01/2.19  Subsumption          : 0.25
% 6.01/2.19  Abstraction          : 0.07
% 6.01/2.19  MUC search           : 0.00
% 6.01/2.19  Cooper               : 0.00
% 6.01/2.19  Total                : 1.47
% 6.01/2.19  Index Insertion      : 0.00
% 6.01/2.19  Index Deletion       : 0.00
% 6.01/2.19  Index Matching       : 0.00
% 6.01/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
