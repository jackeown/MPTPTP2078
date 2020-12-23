%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1177+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:32 EST 2020

% Result     : Theorem 17.59s
% Output     : CNFRefutation 18.01s
% Verified   : 
% Statistics : Number of formulae       :  356 (3675 expanded)
%              Number of leaves         :   49 (1469 expanded)
%              Depth                    :   18
%              Number of atoms          : 1271 (19553 expanded)
%              Number of equality atoms :  209 ( 589 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k9_subset_1 > k3_orders_2 > k6_domain_1 > k3_xboole_0 > k2_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_255,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ( r2_xboole_0(C,D)
                    <=> m1_orders_2(C,A,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_163,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

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
              ( ( v6_orders_2(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( m2_orders_2(C,A,B)
              <=> ( C != k1_xboole_0
                  & r2_wellord1(u1_orders_2(A),C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => k1_funct_1(B,k1_orders_2(A,k3_orders_2(A,C,D))) = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

tff(f_176,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_125,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
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

tff(f_170,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_172,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_202,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ ( B != k1_xboole_0
                & m1_orders_2(B,A,B) )
            & ~ ( ~ m1_orders_2(B,A,B)
                & B = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

tff(f_230,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ( C != D
                   => ( m1_orders_2(C,A,D)
                    <=> ~ m1_orders_2(D,A,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_44,plain,(
    ! [A_66] : ~ r2_xboole_0(A_66,A_66) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_64,plain,(
    m2_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_74,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_72,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_70,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_68,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_66,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_21091,plain,(
    ! [C_685,A_686,B_687] :
      ( v6_orders_2(C_685,A_686)
      | ~ m2_orders_2(C_685,A_686,B_687)
      | ~ m1_orders_1(B_687,k1_orders_1(u1_struct_0(A_686)))
      | ~ l1_orders_2(A_686)
      | ~ v5_orders_2(A_686)
      | ~ v4_orders_2(A_686)
      | ~ v3_orders_2(A_686)
      | v2_struct_0(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_21093,plain,
    ( v6_orders_2('#skF_5','#skF_3')
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_21091])).

tff(c_21098,plain,
    ( v6_orders_2('#skF_5','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_21093])).

tff(c_21099,plain,(
    v6_orders_2('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_21098])).

tff(c_21370,plain,(
    ! [C_700,A_701,B_702] :
      ( m1_subset_1(C_700,k1_zfmisc_1(u1_struct_0(A_701)))
      | ~ m2_orders_2(C_700,A_701,B_702)
      | ~ m1_orders_1(B_702,k1_orders_1(u1_struct_0(A_701)))
      | ~ l1_orders_2(A_701)
      | ~ v5_orders_2(A_701)
      | ~ v4_orders_2(A_701)
      | ~ v3_orders_2(A_701)
      | v2_struct_0(A_701) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_21372,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_21370])).

tff(c_21377,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_21372])).

tff(c_21378,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_21377])).

tff(c_24350,plain,(
    ! [A_815,C_816,B_817] :
      ( r2_wellord1(u1_orders_2(A_815),C_816)
      | ~ m2_orders_2(C_816,A_815,B_817)
      | ~ m1_subset_1(C_816,k1_zfmisc_1(u1_struct_0(A_815)))
      | ~ v6_orders_2(C_816,A_815)
      | ~ m1_orders_1(B_817,k1_orders_1(u1_struct_0(A_815)))
      | ~ l1_orders_2(A_815)
      | ~ v5_orders_2(A_815)
      | ~ v4_orders_2(A_815)
      | ~ v3_orders_2(A_815)
      | v2_struct_0(A_815) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24352,plain,
    ( r2_wellord1(u1_orders_2('#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v6_orders_2('#skF_5','#skF_3')
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_24350])).

tff(c_24357,plain,
    ( r2_wellord1(u1_orders_2('#skF_3'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_21099,c_21378,c_24352])).

tff(c_24358,plain,(
    r2_wellord1(u1_orders_2('#skF_3'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_24357])).

tff(c_30619,plain,(
    ! [A_1034,B_1035,C_1036] :
      ( r2_hidden('#skF_2'(A_1034,B_1035,C_1036),C_1036)
      | m2_orders_2(C_1036,A_1034,B_1035)
      | ~ r2_wellord1(u1_orders_2(A_1034),C_1036)
      | k1_xboole_0 = C_1036
      | ~ m1_subset_1(C_1036,k1_zfmisc_1(u1_struct_0(A_1034)))
      | ~ v6_orders_2(C_1036,A_1034)
      | ~ m1_orders_1(B_1035,k1_orders_1(u1_struct_0(A_1034)))
      | ~ l1_orders_2(A_1034)
      | ~ v5_orders_2(A_1034)
      | ~ v4_orders_2(A_1034)
      | ~ v3_orders_2(A_1034)
      | v2_struct_0(A_1034) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30625,plain,(
    ! [B_1035] :
      ( r2_hidden('#skF_2'('#skF_3',B_1035,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_1035)
      | ~ r2_wellord1(u1_orders_2('#skF_3'),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | ~ v6_orders_2('#skF_5','#skF_3')
      | ~ m1_orders_1(B_1035,k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21378,c_30619])).

tff(c_30640,plain,(
    ! [B_1035] :
      ( r2_hidden('#skF_2'('#skF_3',B_1035,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_1035)
      | k1_xboole_0 = '#skF_5'
      | ~ m1_orders_1(B_1035,k1_orders_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21099,c_24358,c_30625])).

tff(c_30641,plain,(
    ! [B_1035] :
      ( r2_hidden('#skF_2'('#skF_3',B_1035,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_1035)
      | k1_xboole_0 = '#skF_5'
      | ~ m1_orders_1(B_1035,k1_orders_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_30640])).

tff(c_31021,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_30641])).

tff(c_27234,plain,(
    ! [A_915,B_916,C_917] :
      ( r2_hidden('#skF_2'(A_915,B_916,C_917),C_917)
      | m2_orders_2(C_917,A_915,B_916)
      | ~ r2_wellord1(u1_orders_2(A_915),C_917)
      | k1_xboole_0 = C_917
      | ~ m1_subset_1(C_917,k1_zfmisc_1(u1_struct_0(A_915)))
      | ~ v6_orders_2(C_917,A_915)
      | ~ m1_orders_1(B_916,k1_orders_1(u1_struct_0(A_915)))
      | ~ l1_orders_2(A_915)
      | ~ v5_orders_2(A_915)
      | ~ v4_orders_2(A_915)
      | ~ v3_orders_2(A_915)
      | v2_struct_0(A_915) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_27240,plain,(
    ! [B_916] :
      ( r2_hidden('#skF_2'('#skF_3',B_916,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_916)
      | ~ r2_wellord1(u1_orders_2('#skF_3'),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | ~ v6_orders_2('#skF_5','#skF_3')
      | ~ m1_orders_1(B_916,k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21378,c_27234])).

tff(c_27254,plain,(
    ! [B_916] :
      ( r2_hidden('#skF_2'('#skF_3',B_916,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_916)
      | k1_xboole_0 = '#skF_5'
      | ~ m1_orders_1(B_916,k1_orders_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21099,c_24358,c_27240])).

tff(c_27255,plain,(
    ! [B_916] :
      ( r2_hidden('#skF_2'('#skF_3',B_916,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_916)
      | k1_xboole_0 = '#skF_5'
      | ~ m1_orders_1(B_916,k1_orders_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_27254])).

tff(c_27834,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_27255])).

tff(c_50,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_21389,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_21378,c_50])).

tff(c_21707,plain,(
    ! [A_712,C_713,B_714] :
      ( r2_wellord1(u1_orders_2(A_712),C_713)
      | ~ m2_orders_2(C_713,A_712,B_714)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(u1_struct_0(A_712)))
      | ~ v6_orders_2(C_713,A_712)
      | ~ m1_orders_1(B_714,k1_orders_1(u1_struct_0(A_712)))
      | ~ l1_orders_2(A_712)
      | ~ v5_orders_2(A_712)
      | ~ v4_orders_2(A_712)
      | ~ v3_orders_2(A_712)
      | v2_struct_0(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_21709,plain,
    ( r2_wellord1(u1_orders_2('#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v6_orders_2('#skF_5','#skF_3')
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_21707])).

tff(c_21714,plain,
    ( r2_wellord1(u1_orders_2('#skF_3'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_21099,c_21378,c_21709])).

tff(c_21715,plain,(
    r2_wellord1(u1_orders_2('#skF_3'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_21714])).

tff(c_23915,plain,(
    ! [A_787,B_788,C_789] :
      ( r2_hidden('#skF_2'(A_787,B_788,C_789),C_789)
      | m2_orders_2(C_789,A_787,B_788)
      | ~ r2_wellord1(u1_orders_2(A_787),C_789)
      | k1_xboole_0 = C_789
      | ~ m1_subset_1(C_789,k1_zfmisc_1(u1_struct_0(A_787)))
      | ~ v6_orders_2(C_789,A_787)
      | ~ m1_orders_1(B_788,k1_orders_1(u1_struct_0(A_787)))
      | ~ l1_orders_2(A_787)
      | ~ v5_orders_2(A_787)
      | ~ v4_orders_2(A_787)
      | ~ v3_orders_2(A_787)
      | v2_struct_0(A_787) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_23919,plain,(
    ! [B_788] :
      ( r2_hidden('#skF_2'('#skF_3',B_788,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_788)
      | ~ r2_wellord1(u1_orders_2('#skF_3'),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | ~ v6_orders_2('#skF_5','#skF_3')
      | ~ m1_orders_1(B_788,k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21378,c_23915])).

tff(c_23929,plain,(
    ! [B_788] :
      ( r2_hidden('#skF_2'('#skF_3',B_788,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_788)
      | k1_xboole_0 = '#skF_5'
      | ~ m1_orders_1(B_788,k1_orders_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21099,c_21715,c_23919])).

tff(c_23930,plain,(
    ! [B_788] :
      ( r2_hidden('#skF_2'('#skF_3',B_788,'#skF_5'),'#skF_5')
      | m2_orders_2('#skF_5','#skF_3',B_788)
      | k1_xboole_0 = '#skF_5'
      | ~ m1_orders_1(B_788,k1_orders_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_23929])).

tff(c_24152,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_23930])).

tff(c_52,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(A_73,k1_zfmisc_1(B_74))
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_62,plain,(
    m2_orders_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_21374,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_21370])).

tff(c_21381,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_21374])).

tff(c_21382,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_21381])).

tff(c_21410,plain,(
    ! [C_703,A_704] :
      ( k1_xboole_0 = C_703
      | ~ m1_orders_2(C_703,A_704,k1_xboole_0)
      | ~ m1_subset_1(C_703,k1_zfmisc_1(u1_struct_0(A_704)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_704)))
      | ~ l1_orders_2(A_704)
      | ~ v5_orders_2(A_704)
      | ~ v4_orders_2(A_704)
      | ~ v3_orders_2(A_704)
      | v2_struct_0(A_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_21412,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_21382,c_21410])).

tff(c_21420,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21412])).

tff(c_21421,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_21420])).

tff(c_21428,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_21421])).

tff(c_21432,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_21428])).

tff(c_24161,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24152,c_21432])).

tff(c_24168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21389,c_24161])).

tff(c_24170,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_23930])).

tff(c_20228,plain,(
    ! [C_606,A_607,B_608] :
      ( v6_orders_2(C_606,A_607)
      | ~ m2_orders_2(C_606,A_607,B_608)
      | ~ m1_orders_1(B_608,k1_orders_1(u1_struct_0(A_607)))
      | ~ l1_orders_2(A_607)
      | ~ v5_orders_2(A_607)
      | ~ v4_orders_2(A_607)
      | ~ v3_orders_2(A_607)
      | v2_struct_0(A_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_20230,plain,
    ( v6_orders_2('#skF_6','#skF_3')
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_20228])).

tff(c_20233,plain,
    ( v6_orders_2('#skF_6','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_20230])).

tff(c_20234,plain,(
    v6_orders_2('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_20233])).

tff(c_84,plain,
    ( r2_xboole_0('#skF_5','#skF_6')
    | m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_86,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_573,plain,(
    ! [C_163,A_164,B_165] :
      ( m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ m2_orders_2(C_163,A_164,B_165)
      | ~ m1_orders_1(B_165,k1_orders_1(u1_struct_0(A_164)))
      | ~ l1_orders_2(A_164)
      | ~ v5_orders_2(A_164)
      | ~ v4_orders_2(A_164)
      | ~ v3_orders_2(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_577,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_573])).

tff(c_584,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_577])).

tff(c_585,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_584])).

tff(c_575,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_573])).

tff(c_580,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_575])).

tff(c_581,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_580])).

tff(c_4358,plain,(
    ! [A_287,B_288,C_289] :
      ( r2_hidden('#skF_1'(A_287,B_288,C_289),B_288)
      | ~ m1_orders_2(C_289,A_287,B_288)
      | k1_xboole_0 = B_288
      | ~ m1_subset_1(C_289,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ l1_orders_2(A_287)
      | ~ v5_orders_2(A_287)
      | ~ v4_orders_2(A_287)
      | ~ v3_orders_2(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4364,plain,(
    ! [B_288] :
      ( r2_hidden('#skF_1'('#skF_3',B_288,'#skF_5'),B_288)
      | ~ m1_orders_2('#skF_5','#skF_3',B_288)
      | k1_xboole_0 = B_288
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_581,c_4358])).

tff(c_4378,plain,(
    ! [B_288] :
      ( r2_hidden('#skF_1'('#skF_3',B_288,'#skF_5'),B_288)
      | ~ m1_orders_2('#skF_5','#skF_3',B_288)
      | k1_xboole_0 = B_288
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_4364])).

tff(c_10849,plain,(
    ! [B_503] :
      ( r2_hidden('#skF_1'('#skF_3',B_503,'#skF_5'),B_503)
      | ~ m1_orders_2('#skF_5','#skF_3',B_503)
      | k1_xboole_0 = B_503
      | ~ m1_subset_1(B_503,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4378])).

tff(c_10853,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_6','#skF_5'),'#skF_6')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_585,c_10849])).

tff(c_10862,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_6','#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_10853])).

tff(c_10867,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10862])).

tff(c_453,plain,(
    ! [C_154,A_155,B_156] :
      ( v6_orders_2(C_154,A_155)
      | ~ m2_orders_2(C_154,A_155,B_156)
      | ~ m1_orders_1(B_156,k1_orders_1(u1_struct_0(A_155)))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_457,plain,
    ( v6_orders_2('#skF_6','#skF_3')
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_453])).

tff(c_464,plain,
    ( v6_orders_2('#skF_6','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_457])).

tff(c_465,plain,(
    v6_orders_2('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_464])).

tff(c_6995,plain,(
    ! [B_382] :
      ( r2_hidden('#skF_1'('#skF_3',B_382,'#skF_5'),B_382)
      | ~ m1_orders_2('#skF_5','#skF_3',B_382)
      | k1_xboole_0 = B_382
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4378])).

tff(c_6999,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_6','#skF_5'),'#skF_6')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_585,c_6995])).

tff(c_7008,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_6','#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6999])).

tff(c_7011,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7008])).

tff(c_605,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_585,c_50])).

tff(c_1299,plain,(
    ! [A_187,B_188,C_189] :
      ( r2_hidden('#skF_1'(A_187,B_188,C_189),B_188)
      | ~ m1_orders_2(C_189,A_187,B_188)
      | k1_xboole_0 = B_188
      | ~ m1_subset_1(C_189,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_orders_2(A_187)
      | ~ v5_orders_2(A_187)
      | ~ v4_orders_2(A_187)
      | ~ v3_orders_2(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1303,plain,(
    ! [B_188] :
      ( r2_hidden('#skF_1'('#skF_3',B_188,'#skF_5'),B_188)
      | ~ m1_orders_2('#skF_5','#skF_3',B_188)
      | k1_xboole_0 = B_188
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_581,c_1299])).

tff(c_1313,plain,(
    ! [B_188] :
      ( r2_hidden('#skF_1'('#skF_3',B_188,'#skF_5'),B_188)
      | ~ m1_orders_2('#skF_5','#skF_3',B_188)
      | k1_xboole_0 = B_188
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_1303])).

tff(c_2399,plain,(
    ! [B_236] :
      ( r2_hidden('#skF_1'('#skF_3',B_236,'#skF_5'),B_236)
      | ~ m1_orders_2('#skF_5','#skF_3',B_236)
      | k1_xboole_0 = B_236
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1313])).

tff(c_2401,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_6','#skF_5'),'#skF_6')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_585,c_2399])).

tff(c_2409,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_6','#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2401])).

tff(c_2412,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2409])).

tff(c_641,plain,(
    ! [C_171,A_172] :
      ( k1_xboole_0 = C_171
      | ~ m1_orders_2(C_171,A_172,k1_xboole_0)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_orders_2(A_172)
      | ~ v5_orders_2(A_172)
      | ~ v4_orders_2(A_172)
      | ~ v3_orders_2(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_645,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_581,c_641])).

tff(c_655,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_645])).

tff(c_656,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_655])).

tff(c_913,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_917,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_913])).

tff(c_2417,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_917])).

tff(c_2425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_2417])).

tff(c_2427,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2409])).

tff(c_18,plain,(
    ! [A_12,B_24,C_30] :
      ( m1_subset_1('#skF_1'(A_12,B_24,C_30),u1_struct_0(A_12))
      | ~ m1_orders_2(C_30,A_12,B_24)
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12)
      | ~ v4_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_147,plain,(
    ! [A_119,B_120] :
      ( r2_xboole_0(A_119,B_120)
      | B_120 = A_119
      | ~ r1_tarski(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_78,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_140,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_78])).

tff(c_160,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_147,c_140])).

tff(c_165,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_2633,plain,(
    ! [A_242,B_243,C_244] :
      ( k3_orders_2(A_242,B_243,'#skF_1'(A_242,B_243,C_244)) = C_244
      | ~ m1_orders_2(C_244,A_242,B_243)
      | k1_xboole_0 = B_243
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_orders_2(A_242)
      | ~ v5_orders_2(A_242)
      | ~ v4_orders_2(A_242)
      | ~ v3_orders_2(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2637,plain,(
    ! [B_243] :
      ( k3_orders_2('#skF_3',B_243,'#skF_1'('#skF_3',B_243,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_243)
      | k1_xboole_0 = B_243
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_581,c_2633])).

tff(c_2647,plain,(
    ! [B_243] :
      ( k3_orders_2('#skF_3',B_243,'#skF_1'('#skF_3',B_243,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_243)
      | k1_xboole_0 = B_243
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_2637])).

tff(c_4247,plain,(
    ! [B_282] :
      ( k3_orders_2('#skF_3',B_282,'#skF_1'('#skF_3',B_282,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_282)
      | k1_xboole_0 = B_282
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2647])).

tff(c_4249,plain,
    ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_585,c_4247])).

tff(c_4257,plain,
    ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4249])).

tff(c_4258,plain,(
    k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2427,c_4257])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2429,plain,(
    ! [A_237,C_238,B_239] :
      ( k9_subset_1(u1_struct_0(A_237),k2_orders_2(A_237,k6_domain_1(u1_struct_0(A_237),C_238)),B_239) = k3_orders_2(A_237,B_239,C_238)
      | ~ m1_subset_1(C_238,u1_struct_0(A_237))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ l1_orders_2(A_237)
      | ~ v5_orders_2(A_237)
      | ~ v4_orders_2(A_237)
      | ~ v3_orders_2(A_237)
      | v2_struct_0(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [A_68,B_69,C_70] :
      ( k9_subset_1(A_68,B_69,C_70) = k3_xboole_0(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_604,plain,(
    ! [B_69] : k9_subset_1(u1_struct_0('#skF_3'),B_69,'#skF_6') = k3_xboole_0(B_69,'#skF_6') ),
    inference(resolution,[status(thm)],[c_585,c_46])).

tff(c_2444,plain,(
    ! [C_238] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_238)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_238)
      | ~ m1_subset_1(C_238,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2429,c_604])).

tff(c_2489,plain,(
    ! [C_238] :
      ( k3_xboole_0('#skF_6',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_238))) = k3_orders_2('#skF_3','#skF_6',C_238)
      | ~ m1_subset_1(C_238,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_585,c_4,c_2444])).

tff(c_2500,plain,(
    ! [C_240] :
      ( k3_xboole_0('#skF_6',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_240))) = k3_orders_2('#skF_3','#skF_6',C_240)
      | ~ m1_subset_1(C_240,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2489])).

tff(c_48,plain,(
    ! [A_71,B_72] : r1_tarski(k3_xboole_0(A_71,B_72),A_71) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2593,plain,(
    ! [C_240] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',C_240),'#skF_6')
      | ~ m1_subset_1(C_240,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2500,c_48])).

tff(c_4267,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4258,c_2593])).

tff(c_4273,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_4267])).

tff(c_4277,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_4273])).

tff(c_4280,plain,
    ( k1_xboole_0 = '#skF_6'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_585,c_581,c_86,c_4277])).

tff(c_4282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2427,c_4280])).

tff(c_4284,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_30,plain,(
    ! [A_34,B_46] :
      ( ~ m2_orders_2(k1_xboole_0,A_34,B_46)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ v6_orders_2(k1_xboole_0,A_34)
      | ~ m1_orders_1(B_46,k1_orders_1(u1_struct_0(A_34)))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4286,plain,(
    ! [B_46] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_3',B_46)
      | ~ v6_orders_2(k1_xboole_0,'#skF_3')
      | ~ m1_orders_1(B_46,k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4284,c_30])).

tff(c_4299,plain,(
    ! [B_46] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_3',B_46)
      | ~ v6_orders_2(k1_xboole_0,'#skF_3')
      | ~ m1_orders_1(B_46,k1_orders_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_4286])).

tff(c_4300,plain,(
    ! [B_46] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_3',B_46)
      | ~ v6_orders_2(k1_xboole_0,'#skF_3')
      | ~ m1_orders_1(B_46,k1_orders_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4299])).

tff(c_4382,plain,(
    ~ v6_orders_2(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4300])).

tff(c_7022,plain,(
    ~ v6_orders_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7011,c_4382])).

tff(c_7037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_7022])).

tff(c_7039,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7008])).

tff(c_592,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_581,c_50])).

tff(c_6400,plain,(
    ! [A_355,B_356,C_357] :
      ( k3_orders_2(A_355,B_356,'#skF_1'(A_355,B_356,C_357)) = C_357
      | ~ m1_orders_2(C_357,A_355,B_356)
      | k1_xboole_0 = B_356
      | ~ m1_subset_1(C_357,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ l1_orders_2(A_355)
      | ~ v5_orders_2(A_355)
      | ~ v4_orders_2(A_355)
      | ~ v3_orders_2(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8120,plain,(
    ! [A_405,B_406,A_407] :
      ( k3_orders_2(A_405,B_406,'#skF_1'(A_405,B_406,A_407)) = A_407
      | ~ m1_orders_2(A_407,A_405,B_406)
      | k1_xboole_0 = B_406
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_405)))
      | ~ l1_orders_2(A_405)
      | ~ v5_orders_2(A_405)
      | ~ v4_orders_2(A_405)
      | ~ v3_orders_2(A_405)
      | v2_struct_0(A_405)
      | ~ r1_tarski(A_407,u1_struct_0(A_405)) ) ),
    inference(resolution,[status(thm)],[c_52,c_6400])).

tff(c_8124,plain,(
    ! [A_407] :
      ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6',A_407)) = A_407
      | ~ m1_orders_2(A_407,'#skF_3','#skF_6')
      | k1_xboole_0 = '#skF_6'
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_407,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_585,c_8120])).

tff(c_8137,plain,(
    ! [A_407] :
      ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6',A_407)) = A_407
      | ~ m1_orders_2(A_407,'#skF_3','#skF_6')
      | k1_xboole_0 = '#skF_6'
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_407,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_8124])).

tff(c_8144,plain,(
    ! [A_408] :
      ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6',A_408)) = A_408
      | ~ m1_orders_2(A_408,'#skF_3','#skF_6')
      | ~ r1_tarski(A_408,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7039,c_8137])).

tff(c_8153,plain,
    ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_592,c_8144])).

tff(c_8166,plain,(
    k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8153])).

tff(c_5679,plain,(
    ! [A_338,C_339,B_340] :
      ( k9_subset_1(u1_struct_0(A_338),k2_orders_2(A_338,k6_domain_1(u1_struct_0(A_338),C_339)),B_340) = k3_orders_2(A_338,B_340,C_339)
      | ~ m1_subset_1(C_339,u1_struct_0(A_338))
      | ~ m1_subset_1(B_340,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ l1_orders_2(A_338)
      | ~ v5_orders_2(A_338)
      | ~ v4_orders_2(A_338)
      | ~ v3_orders_2(A_338)
      | v2_struct_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5698,plain,(
    ! [C_339] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_339)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_339)
      | ~ m1_subset_1(C_339,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5679,c_604])).

tff(c_5750,plain,(
    ! [C_339] :
      ( k3_xboole_0('#skF_6',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_339))) = k3_orders_2('#skF_3','#skF_6',C_339)
      | ~ m1_subset_1(C_339,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_585,c_4,c_5698])).

tff(c_6454,plain,(
    ! [C_361] :
      ( k3_xboole_0('#skF_6',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_361))) = k3_orders_2('#skF_3','#skF_6',C_361)
      | ~ m1_subset_1(C_361,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5750])).

tff(c_6559,plain,(
    ! [C_361] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',C_361),'#skF_6')
      | ~ m1_subset_1(C_361,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6454,c_48])).

tff(c_8174,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8166,c_6559])).

tff(c_8180,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_8174])).

tff(c_8184,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_8180])).

tff(c_8187,plain,
    ( k1_xboole_0 = '#skF_6'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_585,c_581,c_86,c_8184])).

tff(c_8189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7039,c_8187])).

tff(c_8192,plain,(
    ! [B_409] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_3',B_409)
      | ~ m1_orders_1(B_409,k1_orders_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_4300])).

tff(c_8196,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_8192])).

tff(c_10880,plain,(
    ~ m2_orders_2('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10867,c_8196])).

tff(c_10897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10880])).

tff(c_10899,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10862])).

tff(c_9699,plain,(
    ! [A_463,B_464,C_465] :
      ( k3_orders_2(A_463,B_464,'#skF_1'(A_463,B_464,C_465)) = C_465
      | ~ m1_orders_2(C_465,A_463,B_464)
      | k1_xboole_0 = B_464
      | ~ m1_subset_1(C_465,k1_zfmisc_1(u1_struct_0(A_463)))
      | ~ m1_subset_1(B_464,k1_zfmisc_1(u1_struct_0(A_463)))
      | ~ l1_orders_2(A_463)
      | ~ v5_orders_2(A_463)
      | ~ v4_orders_2(A_463)
      | ~ v3_orders_2(A_463)
      | v2_struct_0(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_11923,plain,(
    ! [A_524,B_525,A_526] :
      ( k3_orders_2(A_524,B_525,'#skF_1'(A_524,B_525,A_526)) = A_526
      | ~ m1_orders_2(A_526,A_524,B_525)
      | k1_xboole_0 = B_525
      | ~ m1_subset_1(B_525,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ l1_orders_2(A_524)
      | ~ v5_orders_2(A_524)
      | ~ v4_orders_2(A_524)
      | ~ v3_orders_2(A_524)
      | v2_struct_0(A_524)
      | ~ r1_tarski(A_526,u1_struct_0(A_524)) ) ),
    inference(resolution,[status(thm)],[c_52,c_9699])).

tff(c_11927,plain,(
    ! [A_526] :
      ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6',A_526)) = A_526
      | ~ m1_orders_2(A_526,'#skF_3','#skF_6')
      | k1_xboole_0 = '#skF_6'
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_526,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_585,c_11923])).

tff(c_11940,plain,(
    ! [A_526] :
      ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6',A_526)) = A_526
      | ~ m1_orders_2(A_526,'#skF_3','#skF_6')
      | k1_xboole_0 = '#skF_6'
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_526,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_11927])).

tff(c_19959,plain,(
    ! [A_563] :
      ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6',A_563)) = A_563
      | ~ m1_orders_2(A_563,'#skF_3','#skF_6')
      | ~ r1_tarski(A_563,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10899,c_11940])).

tff(c_19968,plain,
    ( k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_592,c_19959])).

tff(c_19981,plain,(
    k3_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3','#skF_6','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_19968])).

tff(c_8581,plain,(
    ! [A_420,C_421,B_422] :
      ( k9_subset_1(u1_struct_0(A_420),k2_orders_2(A_420,k6_domain_1(u1_struct_0(A_420),C_421)),B_422) = k3_orders_2(A_420,B_422,C_421)
      | ~ m1_subset_1(C_421,u1_struct_0(A_420))
      | ~ m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0(A_420)))
      | ~ l1_orders_2(A_420)
      | ~ v5_orders_2(A_420)
      | ~ v4_orders_2(A_420)
      | ~ v3_orders_2(A_420)
      | v2_struct_0(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8600,plain,(
    ! [C_421] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_421)),'#skF_6') = k3_orders_2('#skF_3','#skF_6',C_421)
      | ~ m1_subset_1(C_421,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8581,c_604])).

tff(c_8652,plain,(
    ! [C_421] :
      ( k3_xboole_0('#skF_6',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_421))) = k3_orders_2('#skF_3','#skF_6',C_421)
      | ~ m1_subset_1(C_421,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_585,c_4,c_8600])).

tff(c_8665,plain,(
    ! [C_423] :
      ( k3_xboole_0('#skF_6',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_423))) = k3_orders_2('#skF_3','#skF_6',C_423)
      | ~ m1_subset_1(C_423,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_8652])).

tff(c_8716,plain,(
    ! [C_423] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_6',C_423),'#skF_6')
      | ~ m1_subset_1(C_423,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8665,c_48])).

tff(c_19991,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19981,c_8716])).

tff(c_20000,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_19991])).

tff(c_20004,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_20000])).

tff(c_20007,plain,
    ( k1_xboole_0 = '#skF_6'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_585,c_581,c_86,c_20004])).

tff(c_20009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10899,c_20007])).

tff(c_20010,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_20013,plain,(
    m1_orders_2('#skF_6','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20010,c_86])).

tff(c_20076,plain,(
    ! [B_580,A_581] :
      ( ~ m1_orders_2(B_580,A_581,B_580)
      | k1_xboole_0 = B_580
      | ~ m1_subset_1(B_580,k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ l1_orders_2(A_581)
      | ~ v5_orders_2(A_581)
      | ~ v4_orders_2(A_581)
      | ~ v3_orders_2(A_581)
      | v2_struct_0(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_20078,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20013,c_20076])).

tff(c_20081,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_20078])).

tff(c_20082,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_20081])).

tff(c_20083,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_20082])).

tff(c_20154,plain,(
    ! [C_595,A_596,B_597] :
      ( m1_subset_1(C_595,k1_zfmisc_1(u1_struct_0(A_596)))
      | ~ m2_orders_2(C_595,A_596,B_597)
      | ~ m1_orders_1(B_597,k1_orders_1(u1_struct_0(A_596)))
      | ~ l1_orders_2(A_596)
      | ~ v5_orders_2(A_596)
      | ~ v4_orders_2(A_596)
      | ~ v3_orders_2(A_596)
      | v2_struct_0(A_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_20156,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_20154])).

tff(c_20159,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_20156])).

tff(c_20161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_20083,c_20159])).

tff(c_20163,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_20082])).

tff(c_20162,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_20082])).

tff(c_20835,plain,(
    ! [A_635,B_636] :
      ( ~ m2_orders_2('#skF_6',A_635,B_636)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_635)))
      | ~ v6_orders_2('#skF_6',A_635)
      | ~ m1_orders_1(B_636,k1_orders_1(u1_struct_0(A_635)))
      | ~ l1_orders_2(A_635)
      | ~ v5_orders_2(A_635)
      | ~ v4_orders_2(A_635)
      | ~ v3_orders_2(A_635)
      | v2_struct_0(A_635) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20162,c_20162,c_20162,c_30])).

tff(c_20837,plain,(
    ! [B_636] :
      ( ~ m2_orders_2('#skF_6','#skF_3',B_636)
      | ~ v6_orders_2('#skF_6','#skF_3')
      | ~ m1_orders_1(B_636,k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20163,c_20835])).

tff(c_20843,plain,(
    ! [B_636] :
      ( ~ m2_orders_2('#skF_6','#skF_3',B_636)
      | ~ m1_orders_1(B_636,k1_orders_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_20234,c_20837])).

tff(c_20846,plain,(
    ! [B_637] :
      ( ~ m2_orders_2('#skF_6','#skF_3',B_637)
      | ~ m1_orders_1(B_637,k1_orders_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_20843])).

tff(c_20849,plain,(
    ~ m2_orders_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_20846])).

tff(c_20853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20849])).

tff(c_20855,plain,(
    ~ m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_22103,plain,(
    ! [C_724,A_725,D_726,B_727] :
      ( m1_orders_2(C_724,A_725,D_726)
      | m1_orders_2(D_726,A_725,C_724)
      | D_726 = C_724
      | ~ m2_orders_2(D_726,A_725,B_727)
      | ~ m2_orders_2(C_724,A_725,B_727)
      | ~ m1_orders_1(B_727,k1_orders_1(u1_struct_0(A_725)))
      | ~ l1_orders_2(A_725)
      | ~ v5_orders_2(A_725)
      | ~ v4_orders_2(A_725)
      | ~ v3_orders_2(A_725)
      | v2_struct_0(A_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_22107,plain,(
    ! [C_724] :
      ( m1_orders_2(C_724,'#skF_3','#skF_6')
      | m1_orders_2('#skF_6','#skF_3',C_724)
      | C_724 = '#skF_6'
      | ~ m2_orders_2(C_724,'#skF_3','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_22103])).

tff(c_22114,plain,(
    ! [C_724] :
      ( m1_orders_2(C_724,'#skF_3','#skF_6')
      | m1_orders_2('#skF_6','#skF_3',C_724)
      | C_724 = '#skF_6'
      | ~ m2_orders_2(C_724,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_22107])).

tff(c_22172,plain,(
    ! [C_731] :
      ( m1_orders_2(C_731,'#skF_3','#skF_6')
      | m1_orders_2('#skF_6','#skF_3',C_731)
      | C_731 = '#skF_6'
      | ~ m2_orders_2(C_731,'#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_22114])).

tff(c_22175,plain,
    ( m1_orders_2('#skF_5','#skF_3','#skF_6')
    | m1_orders_2('#skF_6','#skF_3','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_64,c_22172])).

tff(c_22181,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_20855,c_22175])).

tff(c_22184,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22181])).

tff(c_20854,plain,(
    r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_22196,plain,(
    r2_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22184,c_20854])).

tff(c_22204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_22196])).

tff(c_22205,plain,(
    m1_orders_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_22181])).

tff(c_20923,plain,(
    ! [A_652,B_653] :
      ( r2_xboole_0(A_652,B_653)
      | B_653 = A_652
      | ~ r1_tarski(A_652,B_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_20864,plain,(
    ! [B_642,A_643] :
      ( ~ r2_xboole_0(B_642,A_643)
      | ~ r2_xboole_0(A_643,B_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20867,plain,(
    ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_20854,c_20864])).

tff(c_20936,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_20923,c_20867])).

tff(c_20941,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_20936])).

tff(c_23575,plain,(
    ! [A_778,B_779,C_780] :
      ( k3_orders_2(A_778,B_779,'#skF_1'(A_778,B_779,C_780)) = C_780
      | ~ m1_orders_2(C_780,A_778,B_779)
      | k1_xboole_0 = B_779
      | ~ m1_subset_1(C_780,k1_zfmisc_1(u1_struct_0(A_778)))
      | ~ m1_subset_1(B_779,k1_zfmisc_1(u1_struct_0(A_778)))
      | ~ l1_orders_2(A_778)
      | ~ v5_orders_2(A_778)
      | ~ v4_orders_2(A_778)
      | ~ v3_orders_2(A_778)
      | v2_struct_0(A_778) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_23577,plain,(
    ! [B_779] :
      ( k3_orders_2('#skF_3',B_779,'#skF_1'('#skF_3',B_779,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_3',B_779)
      | k1_xboole_0 = B_779
      | ~ m1_subset_1(B_779,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21382,c_23575])).

tff(c_23585,plain,(
    ! [B_779] :
      ( k3_orders_2('#skF_3',B_779,'#skF_1'('#skF_3',B_779,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_3',B_779)
      | k1_xboole_0 = B_779
      | ~ m1_subset_1(B_779,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_23577])).

tff(c_24237,plain,(
    ! [B_810] :
      ( k3_orders_2('#skF_3',B_810,'#skF_1'('#skF_3',B_810,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_3',B_810)
      | k1_xboole_0 = B_810
      | ~ m1_subset_1(B_810,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_23585])).

tff(c_24241,plain,
    ( k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_21378,c_24237])).

tff(c_24249,plain,
    ( k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22205,c_24241])).

tff(c_24250,plain,(
    k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_24170,c_24249])).

tff(c_22267,plain,(
    ! [A_735,C_736,B_737] :
      ( k9_subset_1(u1_struct_0(A_735),k2_orders_2(A_735,k6_domain_1(u1_struct_0(A_735),C_736)),B_737) = k3_orders_2(A_735,B_737,C_736)
      | ~ m1_subset_1(C_736,u1_struct_0(A_735))
      | ~ m1_subset_1(B_737,k1_zfmisc_1(u1_struct_0(A_735)))
      | ~ l1_orders_2(A_735)
      | ~ v5_orders_2(A_735)
      | ~ v4_orders_2(A_735)
      | ~ v3_orders_2(A_735)
      | v2_struct_0(A_735) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21388,plain,(
    ! [B_69] : k9_subset_1(u1_struct_0('#skF_3'),B_69,'#skF_5') = k3_xboole_0(B_69,'#skF_5') ),
    inference(resolution,[status(thm)],[c_21378,c_46])).

tff(c_22278,plain,(
    ! [C_736] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_736)),'#skF_5') = k3_orders_2('#skF_3','#skF_5',C_736)
      | ~ m1_subset_1(C_736,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22267,c_21388])).

tff(c_22324,plain,(
    ! [C_736] :
      ( k3_xboole_0('#skF_5',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_736))) = k3_orders_2('#skF_3','#skF_5',C_736)
      | ~ m1_subset_1(C_736,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21378,c_4,c_22278])).

tff(c_22935,plain,(
    ! [C_760] :
      ( k3_xboole_0('#skF_5',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_760))) = k3_orders_2('#skF_3','#skF_5',C_760)
      | ~ m1_subset_1(C_760,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_22324])).

tff(c_23016,plain,(
    ! [C_760] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_760),'#skF_5')
      | ~ m1_subset_1(C_760,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22935,c_48])).

tff(c_24257,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24250,c_23016])).

tff(c_24263,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_20941,c_24257])).

tff(c_24267,plain,
    ( ~ m1_orders_2('#skF_6','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_24263])).

tff(c_24270,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21378,c_21382,c_22205,c_24267])).

tff(c_24272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_24170,c_24270])).

tff(c_24274,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_21421])).

tff(c_24315,plain,(
    ! [A_811,B_812] :
      ( ~ m2_orders_2(k1_xboole_0,A_811,B_812)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_811)))
      | ~ v6_orders_2(k1_xboole_0,A_811)
      | ~ m1_orders_1(B_812,k1_orders_1(u1_struct_0(A_811)))
      | ~ l1_orders_2(A_811)
      | ~ v5_orders_2(A_811)
      | ~ v4_orders_2(A_811)
      | ~ v3_orders_2(A_811)
      | v2_struct_0(A_811) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24317,plain,(
    ! [B_812] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_3',B_812)
      | ~ v6_orders_2(k1_xboole_0,'#skF_3')
      | ~ m1_orders_1(B_812,k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24274,c_24315])).

tff(c_24323,plain,(
    ! [B_812] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_3',B_812)
      | ~ v6_orders_2(k1_xboole_0,'#skF_3')
      | ~ m1_orders_1(B_812,k1_orders_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_24317])).

tff(c_24324,plain,(
    ! [B_812] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_3',B_812)
      | ~ v6_orders_2(k1_xboole_0,'#skF_3')
      | ~ m1_orders_1(B_812,k1_orders_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_24323])).

tff(c_24364,plain,(
    ~ v6_orders_2(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_24324])).

tff(c_27847,plain,(
    ~ v6_orders_2('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27834,c_24364])).

tff(c_27861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21099,c_27847])).

tff(c_27863,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27255])).

tff(c_24624,plain,(
    ! [A_822,B_823,C_824] :
      ( r2_hidden('#skF_1'(A_822,B_823,C_824),B_823)
      | ~ m1_orders_2(C_824,A_822,B_823)
      | k1_xboole_0 = B_823
      | ~ m1_subset_1(C_824,k1_zfmisc_1(u1_struct_0(A_822)))
      | ~ m1_subset_1(B_823,k1_zfmisc_1(u1_struct_0(A_822)))
      | ~ l1_orders_2(A_822)
      | ~ v5_orders_2(A_822)
      | ~ v4_orders_2(A_822)
      | ~ v3_orders_2(A_822)
      | v2_struct_0(A_822) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24628,plain,(
    ! [B_823] :
      ( r2_hidden('#skF_1'('#skF_3',B_823,'#skF_6'),B_823)
      | ~ m1_orders_2('#skF_6','#skF_3',B_823)
      | k1_xboole_0 = B_823
      | ~ m1_subset_1(B_823,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21382,c_24624])).

tff(c_24640,plain,(
    ! [B_823] :
      ( r2_hidden('#skF_1'('#skF_3',B_823,'#skF_6'),B_823)
      | ~ m1_orders_2('#skF_6','#skF_3',B_823)
      | k1_xboole_0 = B_823
      | ~ m1_subset_1(B_823,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_24628])).

tff(c_24647,plain,(
    ! [B_825] :
      ( r2_hidden('#skF_1'('#skF_3',B_825,'#skF_6'),B_825)
      | ~ m1_orders_2('#skF_6','#skF_3',B_825)
      | k1_xboole_0 = B_825
      | ~ m1_subset_1(B_825,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_24640])).

tff(c_24659,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_21378,c_24647])).

tff(c_25051,plain,(
    ~ m1_orders_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24659])).

tff(c_25327,plain,(
    ! [C_848,A_849,D_850,B_851] :
      ( m1_orders_2(C_848,A_849,D_850)
      | m1_orders_2(D_850,A_849,C_848)
      | D_850 = C_848
      | ~ m2_orders_2(D_850,A_849,B_851)
      | ~ m2_orders_2(C_848,A_849,B_851)
      | ~ m1_orders_1(B_851,k1_orders_1(u1_struct_0(A_849)))
      | ~ l1_orders_2(A_849)
      | ~ v5_orders_2(A_849)
      | ~ v4_orders_2(A_849)
      | ~ v3_orders_2(A_849)
      | v2_struct_0(A_849) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_25329,plain,(
    ! [C_848] :
      ( m1_orders_2(C_848,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_848)
      | C_848 = '#skF_5'
      | ~ m2_orders_2(C_848,'#skF_3','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_25327])).

tff(c_25334,plain,(
    ! [C_848] :
      ( m1_orders_2(C_848,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_848)
      | C_848 = '#skF_5'
      | ~ m2_orders_2(C_848,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_25329])).

tff(c_25563,plain,(
    ! [C_859] :
      ( m1_orders_2(C_859,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_859)
      | C_859 = '#skF_5'
      | ~ m2_orders_2(C_859,'#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_25334])).

tff(c_25569,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | m1_orders_2('#skF_5','#skF_3','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_62,c_25563])).

tff(c_25576,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_20855,c_25051,c_25569])).

tff(c_25595,plain,(
    r2_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25576,c_20854])).

tff(c_25603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_25595])).

tff(c_25605,plain,(
    m1_orders_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24659])).

tff(c_26728,plain,(
    ! [A_902,B_903,C_904] :
      ( k3_orders_2(A_902,B_903,'#skF_1'(A_902,B_903,C_904)) = C_904
      | ~ m1_orders_2(C_904,A_902,B_903)
      | k1_xboole_0 = B_903
      | ~ m1_subset_1(C_904,k1_zfmisc_1(u1_struct_0(A_902)))
      | ~ m1_subset_1(B_903,k1_zfmisc_1(u1_struct_0(A_902)))
      | ~ l1_orders_2(A_902)
      | ~ v5_orders_2(A_902)
      | ~ v4_orders_2(A_902)
      | ~ v3_orders_2(A_902)
      | v2_struct_0(A_902) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26732,plain,(
    ! [B_903] :
      ( k3_orders_2('#skF_3',B_903,'#skF_1'('#skF_3',B_903,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_3',B_903)
      | k1_xboole_0 = B_903
      | ~ m1_subset_1(B_903,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21382,c_26728])).

tff(c_26744,plain,(
    ! [B_903] :
      ( k3_orders_2('#skF_3',B_903,'#skF_1'('#skF_3',B_903,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_3',B_903)
      | k1_xboole_0 = B_903
      | ~ m1_subset_1(B_903,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_26732])).

tff(c_28065,plain,(
    ! [B_952] :
      ( k3_orders_2('#skF_3',B_952,'#skF_1'('#skF_3',B_952,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_3',B_952)
      | k1_xboole_0 = B_952
      | ~ m1_subset_1(B_952,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_26744])).

tff(c_28071,plain,
    ( k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_21378,c_28065])).

tff(c_28080,plain,
    ( k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25605,c_28071])).

tff(c_28081,plain,(
    k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_27863,c_28080])).

tff(c_25620,plain,(
    ! [A_860,C_861,B_862] :
      ( k9_subset_1(u1_struct_0(A_860),k2_orders_2(A_860,k6_domain_1(u1_struct_0(A_860),C_861)),B_862) = k3_orders_2(A_860,B_862,C_861)
      | ~ m1_subset_1(C_861,u1_struct_0(A_860))
      | ~ m1_subset_1(B_862,k1_zfmisc_1(u1_struct_0(A_860)))
      | ~ l1_orders_2(A_860)
      | ~ v5_orders_2(A_860)
      | ~ v4_orders_2(A_860)
      | ~ v3_orders_2(A_860)
      | v2_struct_0(A_860) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25639,plain,(
    ! [C_861] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_861)),'#skF_5') = k3_orders_2('#skF_3','#skF_5',C_861)
      | ~ m1_subset_1(C_861,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25620,c_21388])).

tff(c_25691,plain,(
    ! [C_861] :
      ( k3_xboole_0('#skF_5',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_861))) = k3_orders_2('#skF_3','#skF_5',C_861)
      | ~ m1_subset_1(C_861,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21378,c_4,c_25639])).

tff(c_25704,plain,(
    ! [C_863] :
      ( k3_xboole_0('#skF_5',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_863))) = k3_orders_2('#skF_3','#skF_5',C_863)
      | ~ m1_subset_1(C_863,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_25691])).

tff(c_25755,plain,(
    ! [C_863] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_863),'#skF_5')
      | ~ m1_subset_1(C_863,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25704,c_48])).

tff(c_28088,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28081,c_25755])).

tff(c_28094,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_20941,c_28088])).

tff(c_28098,plain,
    ( ~ m1_orders_2('#skF_6','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_28094])).

tff(c_28101,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21378,c_21382,c_25605,c_28098])).

tff(c_28103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_27863,c_28101])).

tff(c_28139,plain,(
    ! [B_957] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_3',B_957)
      | ~ m1_orders_1(B_957,k1_orders_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_24324])).

tff(c_28143,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_28139])).

tff(c_31030,plain,(
    ~ m2_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31021,c_28143])).

tff(c_31047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_31030])).

tff(c_31049,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_30641])).

tff(c_28930,plain,(
    ! [C_973,A_974,D_975,B_976] :
      ( m1_orders_2(C_973,A_974,D_975)
      | m1_orders_2(D_975,A_974,C_973)
      | D_975 = C_973
      | ~ m2_orders_2(D_975,A_974,B_976)
      | ~ m2_orders_2(C_973,A_974,B_976)
      | ~ m1_orders_1(B_976,k1_orders_1(u1_struct_0(A_974)))
      | ~ l1_orders_2(A_974)
      | ~ v5_orders_2(A_974)
      | ~ v4_orders_2(A_974)
      | ~ v3_orders_2(A_974)
      | v2_struct_0(A_974) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_28932,plain,(
    ! [C_973] :
      ( m1_orders_2(C_973,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_973)
      | C_973 = '#skF_5'
      | ~ m2_orders_2(C_973,'#skF_3','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_28930])).

tff(c_28937,plain,(
    ! [C_973] :
      ( m1_orders_2(C_973,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_973)
      | C_973 = '#skF_5'
      | ~ m2_orders_2(C_973,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_28932])).

tff(c_28946,plain,(
    ! [C_977] :
      ( m1_orders_2(C_977,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_977)
      | C_977 = '#skF_5'
      | ~ m2_orders_2(C_977,'#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_28937])).

tff(c_28952,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | m1_orders_2('#skF_5','#skF_3','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_62,c_28946])).

tff(c_28957,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_20855,c_28952])).

tff(c_28958,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_28957])).

tff(c_28976,plain,(
    r2_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28958,c_20854])).

tff(c_28984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_28976])).

tff(c_28985,plain,(
    m1_orders_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_28957])).

tff(c_21402,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_21382,c_50])).

tff(c_29926,plain,(
    ! [A_1014,B_1015,C_1016] :
      ( k3_orders_2(A_1014,B_1015,'#skF_1'(A_1014,B_1015,C_1016)) = C_1016
      | ~ m1_orders_2(C_1016,A_1014,B_1015)
      | k1_xboole_0 = B_1015
      | ~ m1_subset_1(C_1016,k1_zfmisc_1(u1_struct_0(A_1014)))
      | ~ m1_subset_1(B_1015,k1_zfmisc_1(u1_struct_0(A_1014)))
      | ~ l1_orders_2(A_1014)
      | ~ v5_orders_2(A_1014)
      | ~ v4_orders_2(A_1014)
      | ~ v3_orders_2(A_1014)
      | v2_struct_0(A_1014) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_31330,plain,(
    ! [A_1070,B_1071,A_1072] :
      ( k3_orders_2(A_1070,B_1071,'#skF_1'(A_1070,B_1071,A_1072)) = A_1072
      | ~ m1_orders_2(A_1072,A_1070,B_1071)
      | k1_xboole_0 = B_1071
      | ~ m1_subset_1(B_1071,k1_zfmisc_1(u1_struct_0(A_1070)))
      | ~ l1_orders_2(A_1070)
      | ~ v5_orders_2(A_1070)
      | ~ v4_orders_2(A_1070)
      | ~ v3_orders_2(A_1070)
      | v2_struct_0(A_1070)
      | ~ r1_tarski(A_1072,u1_struct_0(A_1070)) ) ),
    inference(resolution,[status(thm)],[c_52,c_29926])).

tff(c_31336,plain,(
    ! [A_1072] :
      ( k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5',A_1072)) = A_1072
      | ~ m1_orders_2(A_1072,'#skF_3','#skF_5')
      | k1_xboole_0 = '#skF_5'
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_1072,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_21378,c_31330])).

tff(c_31351,plain,(
    ! [A_1072] :
      ( k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5',A_1072)) = A_1072
      | ~ m1_orders_2(A_1072,'#skF_3','#skF_5')
      | k1_xboole_0 = '#skF_5'
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_1072,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_31336])).

tff(c_40205,plain,(
    ! [A_1119] :
      ( k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5',A_1119)) = A_1119
      | ~ m1_orders_2(A_1119,'#skF_3','#skF_5')
      | ~ r1_tarski(A_1119,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_31049,c_31351])).

tff(c_40211,plain,
    ( k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_21402,c_40205])).

tff(c_40226,plain,(
    k3_orders_2('#skF_3','#skF_5','#skF_1'('#skF_3','#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28985,c_40211])).

tff(c_28407,plain,(
    ! [A_962,C_963,B_964] :
      ( k9_subset_1(u1_struct_0(A_962),k2_orders_2(A_962,k6_domain_1(u1_struct_0(A_962),C_963)),B_964) = k3_orders_2(A_962,B_964,C_963)
      | ~ m1_subset_1(C_963,u1_struct_0(A_962))
      | ~ m1_subset_1(B_964,k1_zfmisc_1(u1_struct_0(A_962)))
      | ~ l1_orders_2(A_962)
      | ~ v5_orders_2(A_962)
      | ~ v4_orders_2(A_962)
      | ~ v3_orders_2(A_962)
      | v2_struct_0(A_962) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28422,plain,(
    ! [C_963] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_963)),'#skF_5') = k3_orders_2('#skF_3','#skF_5',C_963)
      | ~ m1_subset_1(C_963,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28407,c_21388])).

tff(c_28470,plain,(
    ! [C_963] :
      ( k3_xboole_0('#skF_5',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_963))) = k3_orders_2('#skF_3','#skF_5',C_963)
      | ~ m1_subset_1(C_963,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21378,c_4,c_28422])).

tff(c_28791,plain,(
    ! [C_968] :
      ( k3_xboole_0('#skF_5',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_968))) = k3_orders_2('#skF_3','#skF_5',C_968)
      | ~ m1_subset_1(C_968,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_28470])).

tff(c_28839,plain,(
    ! [C_968] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_968),'#skF_5')
      | ~ m1_subset_1(C_968,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28791,c_48])).

tff(c_40237,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40226,c_28839])).

tff(c_40246,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_20941,c_40237])).

tff(c_40250,plain,
    ( ~ m1_orders_2('#skF_6','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_40246])).

tff(c_40253,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_21378,c_21382,c_28985,c_40250])).

tff(c_40255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_31049,c_40253])).

tff(c_40256,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_20936])).

tff(c_40261,plain,(
    r2_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40256,c_20854])).

tff(c_40264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40261])).

%------------------------------------------------------------------------------
