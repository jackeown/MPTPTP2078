%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:33 EST 2020

% Result     : Theorem 8.86s
% Output     : CNFRefutation 8.86s
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
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

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
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

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
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

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
      ( m1_subset_1(k1_orders_2(A_14359,B_14360),k1_zfmisc_1(u1_struct_0(A_14359)))
      | ~ m1_subset_1(B_14360,k1_zfmisc_1(u1_struct_0(A_14359)))
      | ~ l1_orders_2(A_14359)
      | ~ v5_orders_2(A_14359)
      | ~ v4_orders_2(A_14359)
      | ~ v3_orders_2(A_14359)
      | v2_struct_0(A_14359) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_54,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'))) ),
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
      | ~ m1_subset_1(k1_orders_2('#skF_6',k6_domain_1(u1_struct_0('#skF_6'),'#skF_7')),k1_zfmisc_1(A_62)) ) ),
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
    r2_hidden('#skF_7',k1_orders_2('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9482,c_54])).

tff(c_16982,plain,(
    ! [B_26418,A_26419,C_26420] :
      ( ~ r2_hidden(B_26418,k1_orders_2(A_26419,C_26420))
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
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.86/2.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.86/2.87  
% 8.86/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.86/2.87  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2
% 8.86/2.87  
% 8.86/2.87  %Foreground sorts:
% 8.86/2.87  
% 8.86/2.87  
% 8.86/2.87  %Background operators:
% 8.86/2.87  
% 8.86/2.87  
% 8.86/2.87  %Foreground operators:
% 8.86/2.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.86/2.87  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.86/2.87  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 8.86/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.86/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.86/2.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.86/2.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.86/2.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.86/2.87  tff('#skF_7', type, '#skF_7': $i).
% 8.86/2.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.86/2.87  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.86/2.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.86/2.87  tff('#skF_6', type, '#skF_6': $i).
% 8.86/2.87  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.86/2.87  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.86/2.87  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 8.86/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.86/2.87  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.86/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.86/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.86/2.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.86/2.87  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 8.86/2.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.86/2.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.86/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.86/2.87  
% 8.86/2.88  tff(f_142, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 8.86/2.88  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 8.86/2.88  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 8.86/2.88  tff(f_81, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 8.86/2.88  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 8.86/2.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.86/2.88  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.86/2.88  tff(f_124, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 8.86/2.88  tff(c_66, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/2.88  tff(c_64, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/2.88  tff(c_62, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/2.88  tff(c_60, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/2.88  tff(c_58, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/2.88  tff(c_56, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/2.88  tff(c_191, plain, (![A_72, B_73]: (k6_domain_1(A_72, B_73)=k1_tarski(B_73) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.86/2.88  tff(c_199, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_191])).
% 8.86/2.88  tff(c_200, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_199])).
% 8.86/2.88  tff(c_48, plain, (![A_30, B_32]: (m1_subset_1(k6_domain_1(u1_struct_0(A_30), B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.86/2.88  tff(c_9376, plain, (![A_14359, B_14360]: (m1_subset_1(k1_orders_2(A_14359, B_14360), k1_zfmisc_1(u1_struct_0(A_14359))) | ~m1_subset_1(B_14360, k1_zfmisc_1(u1_struct_0(A_14359))) | ~l1_orders_2(A_14359) | ~v5_orders_2(A_14359) | ~v4_orders_2(A_14359) | ~v3_orders_2(A_14359) | v2_struct_0(A_14359))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.86/2.88  tff(c_54, plain, (r2_hidden('#skF_7', k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/2.88  tff(c_162, plain, (![C_61, A_62, B_63]: (r2_hidden(C_61, A_62) | ~r2_hidden(C_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.86/2.88  tff(c_175, plain, (![A_62]: (r2_hidden('#skF_7', A_62) | ~m1_subset_1(k1_orders_2('#skF_6', k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')), k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_54, c_162])).
% 8.86/2.88  tff(c_9388, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_9376, c_175])).
% 8.86/2.88  tff(c_9417, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_9388])).
% 8.86/2.88  tff(c_9418, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_9417])).
% 8.86/2.88  tff(c_9421, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_9418])).
% 8.86/2.88  tff(c_9440, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_48, c_9421])).
% 8.86/2.88  tff(c_9443, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_56, c_9440])).
% 8.86/2.88  tff(c_9445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_9443])).
% 8.86/2.88  tff(c_9446, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_9418])).
% 8.86/2.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.86/2.88  tff(c_9466, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_9446, c_2])).
% 8.86/2.88  tff(c_9481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_9466])).
% 8.86/2.88  tff(c_9482, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_199])).
% 8.86/2.88  tff(c_10350, plain, (![A_14750, B_14751]: (m1_subset_1(k6_domain_1(u1_struct_0(A_14750), B_14751), k1_zfmisc_1(u1_struct_0(A_14750))) | ~m1_subset_1(B_14751, u1_struct_0(A_14750)) | ~l1_orders_2(A_14750) | ~v3_orders_2(A_14750) | v2_struct_0(A_14750))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.86/2.88  tff(c_10365, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9482, c_10350])).
% 8.86/2.88  tff(c_10370, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_56, c_10365])).
% 8.86/2.88  tff(c_10371, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_10370])).
% 8.86/2.88  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.86/2.88  tff(c_9487, plain, (r2_hidden('#skF_7', k1_orders_2('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_9482, c_54])).
% 8.86/2.88  tff(c_16982, plain, (![B_26418, A_26419, C_26420]: (~r2_hidden(B_26418, k1_orders_2(A_26419, C_26420)) | ~r2_hidden(B_26418, C_26420) | ~m1_subset_1(C_26420, k1_zfmisc_1(u1_struct_0(A_26419))) | ~m1_subset_1(B_26418, u1_struct_0(A_26419)) | ~l1_orders_2(A_26419) | ~v5_orders_2(A_26419) | ~v4_orders_2(A_26419) | ~v3_orders_2(A_26419) | v2_struct_0(A_26419))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.86/2.88  tff(c_17001, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_9487, c_16982])).
% 8.86/2.88  tff(c_17011, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_10371, c_8, c_17001])).
% 8.86/2.88  tff(c_17013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_17011])).
% 8.86/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.86/2.88  
% 8.86/2.88  Inference rules
% 8.86/2.88  ----------------------
% 8.86/2.88  #Ref     : 0
% 8.86/2.88  #Sup     : 1689
% 8.86/2.88  #Fact    : 12
% 8.86/2.88  #Define  : 0
% 8.86/2.88  #Split   : 5
% 8.86/2.88  #Chain   : 0
% 8.86/2.88  #Close   : 0
% 8.86/2.88  
% 8.86/2.88  Ordering : KBO
% 8.86/2.88  
% 8.86/2.88  Simplification rules
% 8.86/2.88  ----------------------
% 8.86/2.88  #Subsume      : 261
% 8.86/2.88  #Demod        : 330
% 8.86/2.88  #Tautology    : 308
% 8.86/2.88  #SimpNegUnit  : 153
% 8.86/2.88  #BackRed      : 3
% 8.86/2.88  
% 8.86/2.88  #Partial instantiations: 13780
% 8.86/2.88  #Strategies tried      : 1
% 8.86/2.88  
% 8.86/2.88  Timing (in seconds)
% 8.86/2.88  ----------------------
% 8.86/2.88  Preprocessing        : 0.34
% 8.86/2.88  Parsing              : 0.17
% 8.86/2.88  CNF conversion       : 0.03
% 8.86/2.88  Main loop            : 1.78
% 8.86/2.88  Inferencing          : 0.93
% 8.86/2.88  Reduction            : 0.38
% 8.86/2.88  Demodulation         : 0.25
% 8.86/2.88  BG Simplification    : 0.07
% 8.86/2.88  Subsumption          : 0.30
% 8.86/2.88  Abstraction          : 0.08
% 8.86/2.88  MUC search           : 0.00
% 8.86/2.88  Cooper               : 0.00
% 8.86/2.88  Total                : 2.15
% 8.86/2.88  Index Insertion      : 0.00
% 8.86/2.88  Index Deletion       : 0.00
% 8.86/2.88  Index Matching       : 0.00
% 8.86/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
