%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:38 EST 2020

% Result     : Theorem 9.84s
% Output     : CNFRefutation 9.94s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 137 expanded)
%              Number of leaves         :   33 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 412 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_64,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_62,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_60,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_58,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_191,plain,(
    ! [A_72,B_73] :
      ( k6_domain_1(A_72,B_73) = k1_tarski(B_73)
      | ~ m1_subset_1(B_73,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_199,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_191])).

tff(c_200,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_48,plain,(
    ! [A_30,B_32] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_30),B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_32,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_9376,plain,(
    ! [A_14359,B_14360] :
      ( m1_subset_1(k2_orders_2(A_14359,B_14360),k1_zfmisc_1(u1_struct_0(A_14359)))
      | ~ m1_subset_1(B_14360,k1_zfmisc_1(u1_struct_0(A_14359)))
      | ~ l1_orders_2(A_14359)
      | ~ v5_orders_2(A_14359)
      | ~ v4_orders_2(A_14359)
      | ~ v3_orders_2(A_14359)
      | v2_struct_0(A_14359) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_54,plain,(
    r2_hidden('#skF_7',k2_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_162,plain,(
    ! [C_61,A_62,B_63] :
      ( r2_hidden(C_61,A_62)
      | ~ r2_hidden(C_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_175,plain,(
    ! [A_62] :
      ( r2_hidden('#skF_7',A_62)
      | ~ m1_subset_1(k2_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7')),k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_54,c_162])).

tff(c_9388,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9376,c_175])).

tff(c_9417,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_9388])).

tff(c_9418,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9417])).

tff(c_9421,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_9418])).

tff(c_9440,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_9421])).

tff(c_9443,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_56,c_9440])).

tff(c_9445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9443])).

tff(c_9446,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_9418])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9466,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9446,c_2])).

tff(c_9481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_9466])).

tff(c_9482,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_10350,plain,(
    ! [A_14750,B_14751] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_14750),B_14751),k1_zfmisc_1(u1_struct_0(A_14750)))
      | ~ m1_subset_1(B_14751,u1_struct_0(A_14750))
      | ~ l1_orders_2(A_14750)
      | ~ v3_orders_2(A_14750)
      | v2_struct_0(A_14750) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10365,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9482,c_10350])).

tff(c_10370,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_56,c_10365])).

tff(c_10371,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_10370])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9487,plain,(
    r2_hidden('#skF_7',k2_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9482,c_54])).

tff(c_16982,plain,(
    ! [B_26418,A_26419,C_26420] :
      ( ~ r2_hidden(B_26418,k2_orders_2(A_26419,C_26420))
      | ~ r2_hidden(B_26418,C_26420)
      | ~ m1_subset_1(C_26420,k1_zfmisc_1(u1_struct_0(A_26419)))
      | ~ m1_subset_1(B_26418,u1_struct_0(A_26419))
      | ~ l1_orders_2(A_26419)
      | ~ v5_orders_2(A_26419)
      | ~ v4_orders_2(A_26419)
      | ~ v3_orders_2(A_26419)
      | v2_struct_0(A_26419) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_17001,plain,
    ( ~ r2_hidden('#skF_7',k1_tarski('#skF_7'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9487,c_16982])).

tff(c_17011,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_10371,c_8,c_17001])).

tff(c_17013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_17011])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.84/3.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.10  
% 9.84/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.10  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2
% 9.84/3.10  
% 9.84/3.10  %Foreground sorts:
% 9.84/3.10  
% 9.84/3.10  
% 9.84/3.10  %Background operators:
% 9.84/3.10  
% 9.84/3.10  
% 9.84/3.10  %Foreground operators:
% 9.84/3.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.84/3.10  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.84/3.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.84/3.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.84/3.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.84/3.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.84/3.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.84/3.10  tff('#skF_7', type, '#skF_7': $i).
% 9.84/3.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.84/3.10  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.84/3.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.84/3.10  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 9.84/3.10  tff('#skF_6', type, '#skF_6': $i).
% 9.84/3.10  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.84/3.10  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.84/3.10  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.84/3.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.84/3.10  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.84/3.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.84/3.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.84/3.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.84/3.10  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 9.84/3.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.84/3.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.84/3.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.84/3.10  
% 9.94/3.11  tff(f_142, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 9.94/3.11  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.94/3.11  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 9.94/3.11  tff(f_81, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 9.94/3.11  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 9.94/3.11  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.94/3.11  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.94/3.11  tff(f_124, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 9.94/3.11  tff(c_66, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.94/3.11  tff(c_64, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.94/3.11  tff(c_62, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.94/3.11  tff(c_60, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.94/3.11  tff(c_58, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.94/3.11  tff(c_56, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.94/3.11  tff(c_191, plain, (![A_72, B_73]: (k6_domain_1(A_72, B_73)=k1_tarski(B_73) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.94/3.11  tff(c_199, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_191])).
% 9.94/3.11  tff(c_200, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_199])).
% 9.94/3.11  tff(c_48, plain, (![A_30, B_32]: (m1_subset_1(k6_domain_1(u1_struct_0(A_30), B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.94/3.11  tff(c_9376, plain, (![A_14359, B_14360]: (m1_subset_1(k2_orders_2(A_14359, B_14360), k1_zfmisc_1(u1_struct_0(A_14359))) | ~m1_subset_1(B_14360, k1_zfmisc_1(u1_struct_0(A_14359))) | ~l1_orders_2(A_14359) | ~v5_orders_2(A_14359) | ~v4_orders_2(A_14359) | ~v3_orders_2(A_14359) | v2_struct_0(A_14359))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.94/3.11  tff(c_54, plain, (r2_hidden('#skF_7', k2_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.94/3.11  tff(c_162, plain, (![C_61, A_62, B_63]: (r2_hidden(C_61, A_62) | ~r2_hidden(C_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.94/3.11  tff(c_175, plain, (![A_62]: (r2_hidden('#skF_7', A_62) | ~m1_subset_1(k2_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')), k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_54, c_162])).
% 9.94/3.11  tff(c_9388, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_9376, c_175])).
% 9.94/3.11  tff(c_9417, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_9388])).
% 9.94/3.11  tff(c_9418, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_9417])).
% 9.94/3.11  tff(c_9421, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_9418])).
% 9.94/3.11  tff(c_9440, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_48, c_9421])).
% 9.94/3.11  tff(c_9443, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_56, c_9440])).
% 9.94/3.11  tff(c_9445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_9443])).
% 9.94/3.11  tff(c_9446, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_9418])).
% 9.94/3.11  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.94/3.11  tff(c_9466, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_9446, c_2])).
% 9.94/3.11  tff(c_9481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_9466])).
% 9.94/3.11  tff(c_9482, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_199])).
% 9.94/3.11  tff(c_10350, plain, (![A_14750, B_14751]: (m1_subset_1(k6_domain_1(u1_struct_0(A_14750), B_14751), k1_zfmisc_1(u1_struct_0(A_14750))) | ~m1_subset_1(B_14751, u1_struct_0(A_14750)) | ~l1_orders_2(A_14750) | ~v3_orders_2(A_14750) | v2_struct_0(A_14750))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.94/3.11  tff(c_10365, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9482, c_10350])).
% 9.94/3.11  tff(c_10370, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_56, c_10365])).
% 9.94/3.11  tff(c_10371, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_10370])).
% 9.94/3.11  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.94/3.11  tff(c_9487, plain, (r2_hidden('#skF_7', k2_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_9482, c_54])).
% 9.94/3.11  tff(c_16982, plain, (![B_26418, A_26419, C_26420]: (~r2_hidden(B_26418, k2_orders_2(A_26419, C_26420)) | ~r2_hidden(B_26418, C_26420) | ~m1_subset_1(C_26420, k1_zfmisc_1(u1_struct_0(A_26419))) | ~m1_subset_1(B_26418, u1_struct_0(A_26419)) | ~l1_orders_2(A_26419) | ~v5_orders_2(A_26419) | ~v4_orders_2(A_26419) | ~v3_orders_2(A_26419) | v2_struct_0(A_26419))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.94/3.11  tff(c_17001, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_9487, c_16982])).
% 9.94/3.11  tff(c_17011, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_10371, c_8, c_17001])).
% 9.94/3.11  tff(c_17013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_17011])).
% 9.94/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.94/3.11  
% 9.94/3.11  Inference rules
% 9.94/3.11  ----------------------
% 9.94/3.11  #Ref     : 0
% 9.94/3.11  #Sup     : 1689
% 9.94/3.11  #Fact    : 12
% 9.94/3.11  #Define  : 0
% 9.94/3.11  #Split   : 5
% 9.94/3.11  #Chain   : 0
% 9.94/3.11  #Close   : 0
% 9.94/3.11  
% 9.94/3.11  Ordering : KBO
% 9.94/3.11  
% 9.94/3.11  Simplification rules
% 9.94/3.11  ----------------------
% 9.94/3.11  #Subsume      : 261
% 9.94/3.11  #Demod        : 330
% 9.94/3.11  #Tautology    : 308
% 9.94/3.11  #SimpNegUnit  : 153
% 9.94/3.11  #BackRed      : 3
% 9.94/3.11  
% 9.94/3.11  #Partial instantiations: 13780
% 9.94/3.11  #Strategies tried      : 1
% 9.94/3.11  
% 9.94/3.11  Timing (in seconds)
% 9.94/3.11  ----------------------
% 9.94/3.11  Preprocessing        : 0.36
% 9.94/3.11  Parsing              : 0.19
% 9.94/3.11  CNF conversion       : 0.03
% 9.94/3.11  Main loop            : 1.98
% 9.94/3.11  Inferencing          : 1.03
% 9.94/3.11  Reduction            : 0.43
% 9.94/3.11  Demodulation         : 0.29
% 9.94/3.11  BG Simplification    : 0.07
% 9.94/3.11  Subsumption          : 0.33
% 9.94/3.11  Abstraction          : 0.09
% 9.94/3.12  MUC search           : 0.00
% 9.94/3.12  Cooper               : 0.00
% 9.94/3.12  Total                : 2.37
% 9.94/3.12  Index Insertion      : 0.00
% 9.94/3.12  Index Deletion       : 0.00
% 9.94/3.12  Index Matching       : 0.00
% 9.94/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
