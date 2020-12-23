%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:05 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 339 expanded)
%              Number of leaves         :   46 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  193 (1130 expanded)
%              Number of equality atoms :   11 ( 113 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_154,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_63,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v6_orders_2(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( m2_orders_2(C,A,B)
              <=> ( C != k1_xboole_0
                  & r2_wellord1(u1_orders_2(A),C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => k1_funct_1(B,k1_orders_2(A,k3_orders_2(A,C,D))) = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_68,plain,(
    v3_orders_2('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_66,plain,(
    v4_orders_2('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    v5_orders_2('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    l1_orders_2('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    m1_orders_1('#skF_11',k1_orders_1(u1_struct_0('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2401,plain,(
    ! [A_324,B_325] :
      ( m2_orders_2('#skF_9'(A_324,B_325),A_324,B_325)
      | ~ m1_orders_1(B_325,k1_orders_1(u1_struct_0(A_324)))
      | ~ l1_orders_2(A_324)
      | ~ v5_orders_2(A_324)
      | ~ v4_orders_2(A_324)
      | ~ v3_orders_2(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2403,plain,
    ( m2_orders_2('#skF_9'('#skF_10','#skF_11'),'#skF_10','#skF_11')
    | ~ l1_orders_2('#skF_10')
    | ~ v5_orders_2('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | ~ v3_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_2401])).

tff(c_2406,plain,
    ( m2_orders_2('#skF_9'('#skF_10','#skF_11'),'#skF_10','#skF_11')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_2403])).

tff(c_2407,plain,(
    m2_orders_2('#skF_9'('#skF_10','#skF_11'),'#skF_10','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2406])).

tff(c_26,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_5'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_111,C_112] :
      ( r2_hidden('#skF_4'(A_111,k3_tarski(A_111),C_112),A_111)
      | ~ r2_hidden(C_112,k3_tarski(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_152,plain,(
    ! [A_116,C_117] :
      ( ~ r1_tarski(A_116,'#skF_4'(A_116,k3_tarski(A_116),C_117))
      | ~ r2_hidden(C_117,k3_tarski(A_116)) ) ),
    inference(resolution,[status(thm)],[c_122,c_22])).

tff(c_1353,plain,(
    ! [C_242] : ~ r2_hidden(C_242,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_152])).

tff(c_1369,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1353])).

tff(c_161,plain,(
    ! [C_117] : ~ r2_hidden(C_117,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_152])).

tff(c_1370,plain,(
    ! [C_117] : ~ r2_hidden(C_117,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_161])).

tff(c_58,plain,(
    k3_tarski(k4_orders_2('#skF_10','#skF_11')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2736,plain,(
    ! [D_360,A_361,B_362] :
      ( r2_hidden(D_360,k4_orders_2(A_361,B_362))
      | ~ m2_orders_2(D_360,A_361,B_362)
      | ~ m1_orders_1(B_362,k1_orders_1(u1_struct_0(A_361)))
      | ~ l1_orders_2(A_361)
      | ~ v5_orders_2(A_361)
      | ~ v4_orders_2(A_361)
      | ~ v3_orders_2(A_361)
      | v2_struct_0(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2738,plain,(
    ! [D_360] :
      ( r2_hidden(D_360,k4_orders_2('#skF_10','#skF_11'))
      | ~ m2_orders_2(D_360,'#skF_10','#skF_11')
      | ~ l1_orders_2('#skF_10')
      | ~ v5_orders_2('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | ~ v3_orders_2('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_60,c_2736])).

tff(c_2741,plain,(
    ! [D_360] :
      ( r2_hidden(D_360,k4_orders_2('#skF_10','#skF_11'))
      | ~ m2_orders_2(D_360,'#skF_10','#skF_11')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_2738])).

tff(c_2743,plain,(
    ! [D_363] :
      ( r2_hidden(D_363,k4_orders_2('#skF_10','#skF_11'))
      | ~ m2_orders_2(D_363,'#skF_10','#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2741])).

tff(c_4,plain,(
    ! [C_17,A_2,D_20] :
      ( r2_hidden(C_17,k3_tarski(A_2))
      | ~ r2_hidden(D_20,A_2)
      | ~ r2_hidden(C_17,D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2764,plain,(
    ! [C_17,D_363] :
      ( r2_hidden(C_17,k3_tarski(k4_orders_2('#skF_10','#skF_11')))
      | ~ r2_hidden(C_17,D_363)
      | ~ m2_orders_2(D_363,'#skF_10','#skF_11') ) ),
    inference(resolution,[status(thm)],[c_2743,c_4])).

tff(c_2776,plain,(
    ! [C_17,D_363] :
      ( r2_hidden(C_17,k1_xboole_0)
      | ~ r2_hidden(C_17,D_363)
      | ~ m2_orders_2(D_363,'#skF_10','#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2764])).

tff(c_2779,plain,(
    ! [C_364,D_365] :
      ( ~ r2_hidden(C_364,D_365)
      | ~ m2_orders_2(D_365,'#skF_10','#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1370,c_2776])).

tff(c_2846,plain,(
    ! [A_366] :
      ( ~ m2_orders_2(A_366,'#skF_10','#skF_11')
      | k1_xboole_0 = A_366 ) ),
    inference(resolution,[status(thm)],[c_26,c_2779])).

tff(c_2850,plain,(
    '#skF_9'('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2407,c_2846])).

tff(c_2852,plain,(
    m2_orders_2(k1_xboole_0,'#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2850,c_2407])).

tff(c_2645,plain,(
    ! [C_349,A_350,B_351] :
      ( v6_orders_2(C_349,A_350)
      | ~ m2_orders_2(C_349,A_350,B_351)
      | ~ m1_orders_1(B_351,k1_orders_1(u1_struct_0(A_350)))
      | ~ l1_orders_2(A_350)
      | ~ v5_orders_2(A_350)
      | ~ v4_orders_2(A_350)
      | ~ v3_orders_2(A_350)
      | v2_struct_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2647,plain,
    ( v6_orders_2('#skF_9'('#skF_10','#skF_11'),'#skF_10')
    | ~ m1_orders_1('#skF_11',k1_orders_1(u1_struct_0('#skF_10')))
    | ~ l1_orders_2('#skF_10')
    | ~ v5_orders_2('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | ~ v3_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2407,c_2645])).

tff(c_2650,plain,
    ( v6_orders_2('#skF_9'('#skF_10','#skF_11'),'#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_2647])).

tff(c_2651,plain,(
    v6_orders_2('#skF_9'('#skF_10','#skF_11'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2650])).

tff(c_2851,plain,(
    v6_orders_2(k1_xboole_0,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2850,c_2651])).

tff(c_4044,plain,(
    ! [C_383,A_384,B_385] :
      ( m1_subset_1(C_383,k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ m2_orders_2(C_383,A_384,B_385)
      | ~ m1_orders_1(B_385,k1_orders_1(u1_struct_0(A_384)))
      | ~ l1_orders_2(A_384)
      | ~ v5_orders_2(A_384)
      | ~ v4_orders_2(A_384)
      | ~ v3_orders_2(A_384)
      | v2_struct_0(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4046,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_10')))
    | ~ m1_orders_1('#skF_11',k1_orders_1(u1_struct_0('#skF_10')))
    | ~ l1_orders_2('#skF_10')
    | ~ v5_orders_2('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | ~ v3_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2852,c_4044])).

tff(c_4049,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_10')))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_4046])).

tff(c_4050,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4049])).

tff(c_4784,plain,(
    ! [A_401,B_402] :
      ( ~ m2_orders_2(k1_xboole_0,A_401,B_402)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_401)))
      | ~ v6_orders_2(k1_xboole_0,A_401)
      | ~ m1_orders_1(B_402,k1_orders_1(u1_struct_0(A_401)))
      | ~ l1_orders_2(A_401)
      | ~ v5_orders_2(A_401)
      | ~ v4_orders_2(A_401)
      | ~ v3_orders_2(A_401)
      | v2_struct_0(A_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4786,plain,(
    ! [B_402] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_10',B_402)
      | ~ v6_orders_2(k1_xboole_0,'#skF_10')
      | ~ m1_orders_1(B_402,k1_orders_1(u1_struct_0('#skF_10')))
      | ~ l1_orders_2('#skF_10')
      | ~ v5_orders_2('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | ~ v3_orders_2('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_4050,c_4784])).

tff(c_4789,plain,(
    ! [B_402] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_10',B_402)
      | ~ m1_orders_1(B_402,k1_orders_1(u1_struct_0('#skF_10')))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_2851,c_4786])).

tff(c_4791,plain,(
    ! [B_403] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_10',B_403)
      | ~ m1_orders_1(B_403,k1_orders_1(u1_struct_0('#skF_10'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4789])).

tff(c_4794,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_60,c_4791])).

tff(c_4798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2852,c_4794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.12  
% 5.69/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.12  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_9
% 5.69/2.12  
% 5.69/2.12  %Foreground sorts:
% 5.69/2.12  
% 5.69/2.12  
% 5.69/2.12  %Background operators:
% 5.69/2.12  
% 5.69/2.12  
% 5.69/2.12  %Foreground operators:
% 5.69/2.12  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 5.69/2.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.69/2.12  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.69/2.12  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.69/2.12  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 5.69/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.12  tff('#skF_11', type, '#skF_11': $i).
% 5.69/2.12  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.69/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.12  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 5.69/2.12  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 5.69/2.12  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.69/2.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.69/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.69/2.12  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 5.69/2.12  tff('#skF_10', type, '#skF_10': $i).
% 5.69/2.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.69/2.12  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.69/2.12  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.69/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.12  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.69/2.12  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 5.69/2.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.69/2.12  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.69/2.12  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 5.69/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.69/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.69/2.12  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 5.69/2.12  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 5.69/2.12  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.69/2.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.69/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.69/2.12  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 5.69/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.12  
% 5.69/2.14  tff(f_172, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 5.69/2.14  tff(f_154, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 5.69/2.14  tff(f_63, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 5.69/2.14  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.69/2.14  tff(f_37, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 5.69/2.14  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.69/2.14  tff(f_118, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 5.69/2.14  tff(f_138, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 5.69/2.14  tff(f_96, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 5.69/2.14  tff(c_70, plain, (~v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.69/2.14  tff(c_68, plain, (v3_orders_2('#skF_10')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.69/2.14  tff(c_66, plain, (v4_orders_2('#skF_10')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.69/2.14  tff(c_64, plain, (v5_orders_2('#skF_10')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.69/2.14  tff(c_62, plain, (l1_orders_2('#skF_10')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.69/2.14  tff(c_60, plain, (m1_orders_1('#skF_11', k1_orders_1(u1_struct_0('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.69/2.14  tff(c_2401, plain, (![A_324, B_325]: (m2_orders_2('#skF_9'(A_324, B_325), A_324, B_325) | ~m1_orders_1(B_325, k1_orders_1(u1_struct_0(A_324))) | ~l1_orders_2(A_324) | ~v5_orders_2(A_324) | ~v4_orders_2(A_324) | ~v3_orders_2(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.69/2.14  tff(c_2403, plain, (m2_orders_2('#skF_9'('#skF_10', '#skF_11'), '#skF_10', '#skF_11') | ~l1_orders_2('#skF_10') | ~v5_orders_2('#skF_10') | ~v4_orders_2('#skF_10') | ~v3_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_60, c_2401])).
% 5.69/2.14  tff(c_2406, plain, (m2_orders_2('#skF_9'('#skF_10', '#skF_11'), '#skF_10', '#skF_11') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_2403])).
% 5.69/2.14  tff(c_2407, plain, (m2_orders_2('#skF_9'('#skF_10', '#skF_11'), '#skF_10', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_70, c_2406])).
% 5.69/2.14  tff(c_26, plain, (![A_23]: (r2_hidden('#skF_5'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.69/2.14  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.69/2.14  tff(c_122, plain, (![A_111, C_112]: (r2_hidden('#skF_4'(A_111, k3_tarski(A_111), C_112), A_111) | ~r2_hidden(C_112, k3_tarski(A_111)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.14  tff(c_22, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.69/2.14  tff(c_152, plain, (![A_116, C_117]: (~r1_tarski(A_116, '#skF_4'(A_116, k3_tarski(A_116), C_117)) | ~r2_hidden(C_117, k3_tarski(A_116)))), inference(resolution, [status(thm)], [c_122, c_22])).
% 5.69/2.14  tff(c_1353, plain, (![C_242]: (~r2_hidden(C_242, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2, c_152])).
% 5.69/2.14  tff(c_1369, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_1353])).
% 5.69/2.14  tff(c_161, plain, (![C_117]: (~r2_hidden(C_117, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2, c_152])).
% 5.69/2.14  tff(c_1370, plain, (![C_117]: (~r2_hidden(C_117, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_161])).
% 5.69/2.14  tff(c_58, plain, (k3_tarski(k4_orders_2('#skF_10', '#skF_11'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.69/2.14  tff(c_2736, plain, (![D_360, A_361, B_362]: (r2_hidden(D_360, k4_orders_2(A_361, B_362)) | ~m2_orders_2(D_360, A_361, B_362) | ~m1_orders_1(B_362, k1_orders_1(u1_struct_0(A_361))) | ~l1_orders_2(A_361) | ~v5_orders_2(A_361) | ~v4_orders_2(A_361) | ~v3_orders_2(A_361) | v2_struct_0(A_361))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.69/2.14  tff(c_2738, plain, (![D_360]: (r2_hidden(D_360, k4_orders_2('#skF_10', '#skF_11')) | ~m2_orders_2(D_360, '#skF_10', '#skF_11') | ~l1_orders_2('#skF_10') | ~v5_orders_2('#skF_10') | ~v4_orders_2('#skF_10') | ~v3_orders_2('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_60, c_2736])).
% 5.69/2.14  tff(c_2741, plain, (![D_360]: (r2_hidden(D_360, k4_orders_2('#skF_10', '#skF_11')) | ~m2_orders_2(D_360, '#skF_10', '#skF_11') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_2738])).
% 5.69/2.14  tff(c_2743, plain, (![D_363]: (r2_hidden(D_363, k4_orders_2('#skF_10', '#skF_11')) | ~m2_orders_2(D_363, '#skF_10', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_70, c_2741])).
% 5.69/2.14  tff(c_4, plain, (![C_17, A_2, D_20]: (r2_hidden(C_17, k3_tarski(A_2)) | ~r2_hidden(D_20, A_2) | ~r2_hidden(C_17, D_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.14  tff(c_2764, plain, (![C_17, D_363]: (r2_hidden(C_17, k3_tarski(k4_orders_2('#skF_10', '#skF_11'))) | ~r2_hidden(C_17, D_363) | ~m2_orders_2(D_363, '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_2743, c_4])).
% 5.69/2.14  tff(c_2776, plain, (![C_17, D_363]: (r2_hidden(C_17, k1_xboole_0) | ~r2_hidden(C_17, D_363) | ~m2_orders_2(D_363, '#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2764])).
% 5.69/2.14  tff(c_2779, plain, (![C_364, D_365]: (~r2_hidden(C_364, D_365) | ~m2_orders_2(D_365, '#skF_10', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_1370, c_2776])).
% 5.69/2.14  tff(c_2846, plain, (![A_366]: (~m2_orders_2(A_366, '#skF_10', '#skF_11') | k1_xboole_0=A_366)), inference(resolution, [status(thm)], [c_26, c_2779])).
% 5.69/2.14  tff(c_2850, plain, ('#skF_9'('#skF_10', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_2407, c_2846])).
% 5.69/2.14  tff(c_2852, plain, (m2_orders_2(k1_xboole_0, '#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_2850, c_2407])).
% 5.69/2.14  tff(c_2645, plain, (![C_349, A_350, B_351]: (v6_orders_2(C_349, A_350) | ~m2_orders_2(C_349, A_350, B_351) | ~m1_orders_1(B_351, k1_orders_1(u1_struct_0(A_350))) | ~l1_orders_2(A_350) | ~v5_orders_2(A_350) | ~v4_orders_2(A_350) | ~v3_orders_2(A_350) | v2_struct_0(A_350))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.69/2.14  tff(c_2647, plain, (v6_orders_2('#skF_9'('#skF_10', '#skF_11'), '#skF_10') | ~m1_orders_1('#skF_11', k1_orders_1(u1_struct_0('#skF_10'))) | ~l1_orders_2('#skF_10') | ~v5_orders_2('#skF_10') | ~v4_orders_2('#skF_10') | ~v3_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2407, c_2645])).
% 5.69/2.14  tff(c_2650, plain, (v6_orders_2('#skF_9'('#skF_10', '#skF_11'), '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_2647])).
% 5.69/2.14  tff(c_2651, plain, (v6_orders_2('#skF_9'('#skF_10', '#skF_11'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_70, c_2650])).
% 5.69/2.14  tff(c_2851, plain, (v6_orders_2(k1_xboole_0, '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2850, c_2651])).
% 5.69/2.14  tff(c_4044, plain, (![C_383, A_384, B_385]: (m1_subset_1(C_383, k1_zfmisc_1(u1_struct_0(A_384))) | ~m2_orders_2(C_383, A_384, B_385) | ~m1_orders_1(B_385, k1_orders_1(u1_struct_0(A_384))) | ~l1_orders_2(A_384) | ~v5_orders_2(A_384) | ~v4_orders_2(A_384) | ~v3_orders_2(A_384) | v2_struct_0(A_384))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.69/2.14  tff(c_4046, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_10'))) | ~m1_orders_1('#skF_11', k1_orders_1(u1_struct_0('#skF_10'))) | ~l1_orders_2('#skF_10') | ~v5_orders_2('#skF_10') | ~v4_orders_2('#skF_10') | ~v3_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2852, c_4044])).
% 5.69/2.14  tff(c_4049, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_10'))) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_4046])).
% 5.69/2.14  tff(c_4050, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_70, c_4049])).
% 5.69/2.14  tff(c_4784, plain, (![A_401, B_402]: (~m2_orders_2(k1_xboole_0, A_401, B_402) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_401))) | ~v6_orders_2(k1_xboole_0, A_401) | ~m1_orders_1(B_402, k1_orders_1(u1_struct_0(A_401))) | ~l1_orders_2(A_401) | ~v5_orders_2(A_401) | ~v4_orders_2(A_401) | ~v3_orders_2(A_401) | v2_struct_0(A_401))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.69/2.14  tff(c_4786, plain, (![B_402]: (~m2_orders_2(k1_xboole_0, '#skF_10', B_402) | ~v6_orders_2(k1_xboole_0, '#skF_10') | ~m1_orders_1(B_402, k1_orders_1(u1_struct_0('#skF_10'))) | ~l1_orders_2('#skF_10') | ~v5_orders_2('#skF_10') | ~v4_orders_2('#skF_10') | ~v3_orders_2('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_4050, c_4784])).
% 5.69/2.14  tff(c_4789, plain, (![B_402]: (~m2_orders_2(k1_xboole_0, '#skF_10', B_402) | ~m1_orders_1(B_402, k1_orders_1(u1_struct_0('#skF_10'))) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_2851, c_4786])).
% 5.69/2.14  tff(c_4791, plain, (![B_403]: (~m2_orders_2(k1_xboole_0, '#skF_10', B_403) | ~m1_orders_1(B_403, k1_orders_1(u1_struct_0('#skF_10'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_4789])).
% 5.69/2.14  tff(c_4794, plain, (~m2_orders_2(k1_xboole_0, '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_60, c_4791])).
% 5.69/2.14  tff(c_4798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2852, c_4794])).
% 5.69/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.14  
% 5.69/2.14  Inference rules
% 5.69/2.14  ----------------------
% 5.69/2.14  #Ref     : 0
% 5.69/2.14  #Sup     : 1077
% 5.69/2.14  #Fact    : 0
% 5.69/2.14  #Define  : 0
% 5.69/2.14  #Split   : 1
% 5.69/2.14  #Chain   : 0
% 5.69/2.14  #Close   : 0
% 5.69/2.14  
% 5.69/2.14  Ordering : KBO
% 5.69/2.14  
% 5.69/2.14  Simplification rules
% 5.69/2.14  ----------------------
% 5.69/2.14  #Subsume      : 366
% 5.69/2.14  #Demod        : 649
% 5.69/2.14  #Tautology    : 185
% 5.69/2.14  #SimpNegUnit  : 163
% 5.69/2.14  #BackRed      : 8
% 5.69/2.14  
% 5.69/2.14  #Partial instantiations: 0
% 5.69/2.14  #Strategies tried      : 1
% 5.69/2.14  
% 5.69/2.14  Timing (in seconds)
% 5.69/2.14  ----------------------
% 5.69/2.14  Preprocessing        : 0.36
% 5.69/2.14  Parsing              : 0.20
% 5.69/2.14  CNF conversion       : 0.03
% 5.69/2.14  Main loop            : 0.96
% 5.84/2.14  Inferencing          : 0.30
% 5.84/2.14  Reduction            : 0.29
% 5.84/2.14  Demodulation         : 0.19
% 5.84/2.14  BG Simplification    : 0.04
% 5.84/2.14  Subsumption          : 0.25
% 5.84/2.14  Abstraction          : 0.05
% 5.84/2.14  MUC search           : 0.00
% 5.84/2.14  Cooper               : 0.00
% 5.84/2.14  Total                : 1.35
% 5.84/2.14  Index Insertion      : 0.00
% 5.84/2.14  Index Deletion       : 0.00
% 5.84/2.14  Index Matching       : 0.00
% 5.84/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
