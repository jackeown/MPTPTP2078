%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1161+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:31 EST 2020

% Result     : Theorem 14.07s
% Output     : CNFRefutation 14.07s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 648 expanded)
%              Number of leaves         :   43 ( 247 expanded)
%              Depth                    :   22
%              Number of atoms          :  290 (2371 expanded)
%              Number of equality atoms :   39 ( 204 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k9_subset_1 > k3_orders_2 > k6_domain_1 > k3_xboole_0 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1

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

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ r2_hidden(B,k3_orders_2(A,C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_121,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_40,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k3_orders_2(A,B,C) = k9_subset_1(u1_struct_0(A),k2_orders_2(A,k6_domain_1(u1_struct_0(A),C)),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ~ r2_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

tff(c_68,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_74,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_72,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_70,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_38,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_92,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_100,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_92])).

tff(c_106,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_40,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(u1_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_109,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_106,c_40])).

tff(c_112,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_109])).

tff(c_115,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_115])).

tff(c_121,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_120,plain,(
    k6_domain_1(u1_struct_0('#skF_7'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_126,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k6_domain_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_134,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_126])).

tff(c_138,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_134])).

tff(c_139,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_138])).

tff(c_2623,plain,(
    ! [D_234,B_235,C_236] :
      ( r2_hidden('#skF_6'(D_234,B_235,C_236,D_234),C_236)
      | r2_hidden(D_234,a_2_1_orders_2(B_235,C_236))
      | ~ m1_subset_1(D_234,u1_struct_0(B_235))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(u1_struct_0(B_235)))
      | ~ l1_orders_2(B_235)
      | ~ v5_orders_2(B_235)
      | ~ v4_orders_2(B_235)
      | ~ v3_orders_2(B_235)
      | v2_struct_0(B_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2629,plain,(
    ! [D_234] :
      ( r2_hidden('#skF_6'(D_234,'#skF_7',k1_tarski('#skF_8'),D_234),k1_tarski('#skF_8'))
      | r2_hidden(D_234,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_139,c_2623])).

tff(c_2645,plain,(
    ! [D_234] :
      ( r2_hidden('#skF_6'(D_234,'#skF_7',k1_tarski('#skF_8'),D_234),k1_tarski('#skF_8'))
      | r2_hidden(D_234,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_2629])).

tff(c_2653,plain,(
    ! [D_238] :
      ( r2_hidden('#skF_6'(D_238,'#skF_7',k1_tarski('#skF_8'),D_238),k1_tarski('#skF_8'))
      | r2_hidden(D_238,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(D_238,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2645])).

tff(c_6,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2668,plain,(
    ! [D_239] :
      ( '#skF_6'(D_239,'#skF_7',k1_tarski('#skF_8'),D_239) = '#skF_8'
      | r2_hidden(D_239,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2653,c_6])).

tff(c_50,plain,(
    ! [A_26,B_27,C_28] :
      ( '#skF_5'(A_26,B_27,C_28) = A_26
      | ~ r2_hidden(A_26,a_2_1_orders_2(B_27,C_28))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(B_27)))
      | ~ l1_orders_2(B_27)
      | ~ v5_orders_2(B_27)
      | ~ v4_orders_2(B_27)
      | ~ v3_orders_2(B_27)
      | v2_struct_0(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2676,plain,(
    ! [D_239] :
      ( '#skF_5'(D_239,'#skF_7',k1_tarski('#skF_8')) = D_239
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | '#skF_6'(D_239,'#skF_7',k1_tarski('#skF_8'),D_239) = '#skF_8'
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2668,c_50])).

tff(c_2692,plain,(
    ! [D_239] :
      ( '#skF_5'(D_239,'#skF_7',k1_tarski('#skF_8')) = D_239
      | v2_struct_0('#skF_7')
      | '#skF_6'(D_239,'#skF_7',k1_tarski('#skF_8'),D_239) = '#skF_8'
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_139,c_2676])).

tff(c_2695,plain,(
    ! [D_240] :
      ( '#skF_5'(D_240,'#skF_7',k1_tarski('#skF_8')) = D_240
      | '#skF_6'(D_240,'#skF_7',k1_tarski('#skF_8'),D_240) = '#skF_8'
      | ~ m1_subset_1(D_240,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2692])).

tff(c_2729,plain,
    ( '#skF_5'('#skF_8','#skF_7',k1_tarski('#skF_8')) = '#skF_8'
    | '#skF_6'('#skF_8','#skF_7',k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_66,c_2695])).

tff(c_2730,plain,(
    '#skF_6'('#skF_8','#skF_7',k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2729])).

tff(c_2896,plain,(
    ! [B_247,D_248,C_249] :
      ( ~ r2_orders_2(B_247,D_248,'#skF_6'(D_248,B_247,C_249,D_248))
      | r2_hidden(D_248,a_2_1_orders_2(B_247,C_249))
      | ~ m1_subset_1(D_248,u1_struct_0(B_247))
      | ~ m1_subset_1(C_249,k1_zfmisc_1(u1_struct_0(B_247)))
      | ~ l1_orders_2(B_247)
      | ~ v5_orders_2(B_247)
      | ~ v4_orders_2(B_247)
      | ~ v3_orders_2(B_247)
      | v2_struct_0(B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2900,plain,
    ( ~ r2_orders_2('#skF_7','#skF_8','#skF_8')
    | r2_hidden('#skF_8',a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2730,c_2896])).

tff(c_2907,plain,
    ( ~ r2_orders_2('#skF_7','#skF_8','#skF_8')
    | r2_hidden('#skF_8',a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_139,c_66,c_2900])).

tff(c_2908,plain,
    ( ~ r2_orders_2('#skF_7','#skF_8','#skF_8')
    | r2_hidden('#skF_8',a_2_1_orders_2('#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2907])).

tff(c_2912,plain,(
    ~ r2_orders_2('#skF_7','#skF_8','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2908])).

tff(c_8,plain,(
    ! [C_15] : r2_hidden(C_15,k1_tarski(C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    r2_hidden('#skF_8',k3_orders_2('#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_693,plain,(
    ! [A_133,B_134] :
      ( k2_orders_2(A_133,B_134) = a_2_1_orders_2(A_133,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_699,plain,
    ( k2_orders_2('#skF_7',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_7',k1_tarski('#skF_8'))
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_139,c_693])).

tff(c_713,plain,
    ( k2_orders_2('#skF_7',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_7',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_699])).

tff(c_714,plain,(
    k2_orders_2('#skF_7',k1_tarski('#skF_8')) = a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_713])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_3713,plain,(
    ! [A_284,C_285,B_286] :
      ( k9_subset_1(u1_struct_0(A_284),k2_orders_2(A_284,k6_domain_1(u1_struct_0(A_284),C_285)),B_286) = k3_orders_2(A_284,B_286,C_285)
      | ~ m1_subset_1(C_285,u1_struct_0(A_284))
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_orders_2(A_284)
      | ~ v5_orders_2(A_284)
      | ~ v4_orders_2(A_284)
      | ~ v3_orders_2(A_284)
      | v2_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_164,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(A_79,B_80,C_81) = k3_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_173,plain,(
    ! [B_80] : k9_subset_1(u1_struct_0('#skF_7'),B_80,'#skF_9') = k3_xboole_0(B_80,'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_164])).

tff(c_3736,plain,(
    ! [C_285] :
      ( k3_xboole_0(k2_orders_2('#skF_7',k6_domain_1(u1_struct_0('#skF_7'),C_285)),'#skF_9') = k3_orders_2('#skF_7','#skF_9',C_285)
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3713,c_173])).

tff(c_3780,plain,(
    ! [C_285] :
      ( k3_xboole_0(k2_orders_2('#skF_7',k6_domain_1(u1_struct_0('#skF_7'),C_285)),'#skF_9') = k3_orders_2('#skF_7','#skF_9',C_285)
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_64,c_3736])).

tff(c_3804,plain,(
    ! [C_287] :
      ( k3_xboole_0(k2_orders_2('#skF_7',k6_domain_1(u1_struct_0('#skF_7'),C_287)),'#skF_9') = k3_orders_2('#skF_7','#skF_9',C_287)
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3780])).

tff(c_3929,plain,
    ( k3_xboole_0(k2_orders_2('#skF_7',k1_tarski('#skF_8')),'#skF_9') = k3_orders_2('#skF_7','#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_3804])).

tff(c_3933,plain,(
    k3_xboole_0(a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')),'#skF_9') = k3_orders_2('#skF_7','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_714,c_3929])).

tff(c_22,plain,(
    ! [D_21,A_16,B_17] :
      ( r2_hidden(D_21,A_16)
      | ~ r2_hidden(D_21,k3_xboole_0(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4044,plain,(
    ! [D_21] :
      ( r2_hidden(D_21,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
      | ~ r2_hidden(D_21,k3_orders_2('#skF_7','#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3933,c_22])).

tff(c_4276,plain,(
    ! [D_289] :
      ( r2_hidden(D_289,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
      | ~ r2_hidden(D_289,k3_orders_2('#skF_7','#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3933,c_22])).

tff(c_4282,plain,(
    ! [D_289] :
      ( '#skF_5'(D_289,'#skF_7',k1_tarski('#skF_8')) = D_289
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ r2_hidden(D_289,k3_orders_2('#skF_7','#skF_9','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_4276,c_50])).

tff(c_4306,plain,(
    ! [D_289] :
      ( '#skF_5'(D_289,'#skF_7',k1_tarski('#skF_8')) = D_289
      | v2_struct_0('#skF_7')
      | ~ r2_hidden(D_289,k3_orders_2('#skF_7','#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_139,c_4282])).

tff(c_4314,plain,(
    ! [D_290] :
      ( '#skF_5'(D_290,'#skF_7',k1_tarski('#skF_8')) = D_290
      | ~ r2_hidden(D_290,k3_orders_2('#skF_7','#skF_9','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4306])).

tff(c_4508,plain,(
    '#skF_5'('#skF_8','#skF_7',k1_tarski('#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_62,c_4314])).

tff(c_19527,plain,(
    ! [B_570,A_571,C_572,E_573] :
      ( r2_orders_2(B_570,'#skF_5'(A_571,B_570,C_572),E_573)
      | ~ r2_hidden(E_573,C_572)
      | ~ m1_subset_1(E_573,u1_struct_0(B_570))
      | ~ r2_hidden(A_571,a_2_1_orders_2(B_570,C_572))
      | ~ m1_subset_1(C_572,k1_zfmisc_1(u1_struct_0(B_570)))
      | ~ l1_orders_2(B_570)
      | ~ v5_orders_2(B_570)
      | ~ v4_orders_2(B_570)
      | ~ v3_orders_2(B_570)
      | v2_struct_0(B_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_19533,plain,(
    ! [A_571,E_573] :
      ( r2_orders_2('#skF_7','#skF_5'(A_571,'#skF_7',k1_tarski('#skF_8')),E_573)
      | ~ r2_hidden(E_573,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_573,u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_571,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_139,c_19527])).

tff(c_19549,plain,(
    ! [A_571,E_573] :
      ( r2_orders_2('#skF_7','#skF_5'(A_571,'#skF_7',k1_tarski('#skF_8')),E_573)
      | ~ r2_hidden(E_573,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_573,u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_571,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8')))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_19533])).

tff(c_25859,plain,(
    ! [A_679,E_680] :
      ( r2_orders_2('#skF_7','#skF_5'(A_679,'#skF_7',k1_tarski('#skF_8')),E_680)
      | ~ r2_hidden(E_680,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_680,u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_679,a_2_1_orders_2('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_19549])).

tff(c_25868,plain,(
    ! [E_680] :
      ( r2_orders_2('#skF_7','#skF_8',E_680)
      | ~ r2_hidden(E_680,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_680,u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_8',a_2_1_orders_2('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4508,c_25859])).

tff(c_26446,plain,(
    ~ r2_hidden('#skF_8',a_2_1_orders_2('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_25868])).

tff(c_26519,plain,(
    ~ r2_hidden('#skF_8',k3_orders_2('#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_4044,c_26446])).

tff(c_26529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_26519])).

tff(c_26544,plain,(
    ! [E_698] :
      ( r2_orders_2('#skF_7','#skF_8',E_698)
      | ~ r2_hidden(E_698,k1_tarski('#skF_8'))
      | ~ m1_subset_1(E_698,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_25868])).

tff(c_26727,plain,
    ( r2_orders_2('#skF_7','#skF_8','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_8,c_26544])).

tff(c_26775,plain,(
    r2_orders_2('#skF_7','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26727])).

tff(c_26777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2912,c_26775])).

tff(c_26779,plain,(
    r2_orders_2('#skF_7','#skF_8','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2908])).

tff(c_54,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r2_orders_2(A_39,B_40,B_40)
      | ~ m1_subset_1(C_41,u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_26781,plain,(
    ! [C_41] :
      ( ~ m1_subset_1(C_41,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26779,c_54])).

tff(c_26784,plain,(
    ! [C_41] : ~ m1_subset_1(C_41,u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_26781])).

tff(c_26799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26784,c_66])).

%------------------------------------------------------------------------------
