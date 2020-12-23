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
% DateTime   : Thu Dec  3 10:19:50 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  154 (1158 expanded)
%              Number of leaves         :   24 ( 456 expanded)
%              Depth                    :   16
%              Number of atoms          :  547 (6524 expanded)
%              Number of equality atoms :   92 ( 844 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( B != k1_xboole_0
                    & m1_orders_2(B,A,C)
                    & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_60,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ~ r2_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_12,plain,(
    ! [A_1,B_13,C_19] :
      ( m1_subset_1('#skF_1'(A_1,B_13,C_19),u1_struct_0(A_1))
      | ~ m1_orders_2(C_19,A_1,B_13)
      | k1_xboole_0 = B_13
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_435,plain,(
    ! [A_110,B_111,C_112] :
      ( k3_orders_2(A_110,B_111,'#skF_1'(A_110,B_111,C_112)) = C_112
      | ~ m1_orders_2(C_112,A_110,B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_439,plain,(
    ! [B_111] :
      ( k3_orders_2('#skF_2',B_111,'#skF_1'('#skF_2',B_111,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_435])).

tff(c_448,plain,(
    ! [B_111] :
      ( k3_orders_2('#skF_2',B_111,'#skF_1'('#skF_2',B_111,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_439])).

tff(c_454,plain,(
    ! [B_113] :
      ( k3_orders_2('#skF_2',B_113,'#skF_1'('#skF_2',B_113,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_113)
      | k1_xboole_0 = B_113
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_448])).

tff(c_460,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_454])).

tff(c_466,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_460])).

tff(c_467,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_466])).

tff(c_20,plain,(
    ! [B_38,D_44,A_30,C_42] :
      ( r2_hidden(B_38,D_44)
      | ~ r2_hidden(B_38,k3_orders_2(A_30,D_44,C_42))
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(C_42,u1_struct_0(A_30))
      | ~ m1_subset_1(B_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_472,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_20])).

tff(c_479,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_472])).

tff(c_480,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_479])).

tff(c_482,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_485,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_482])).

tff(c_488,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_30,c_24,c_485])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_28,c_488])).

tff(c_492,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_338,plain,(
    ! [A_93,B_94,C_95] :
      ( r2_hidden('#skF_1'(A_93,B_94,C_95),B_94)
      | ~ m1_orders_2(C_95,A_93,B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_342,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_1'('#skF_2',B_94,'#skF_4'),B_94)
      | ~ m1_orders_2('#skF_4','#skF_2',B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_338])).

tff(c_351,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_1'('#skF_2',B_94,'#skF_4'),B_94)
      | ~ m1_orders_2('#skF_4','#skF_2',B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_342])).

tff(c_398,plain,(
    ! [B_101] :
      ( r2_hidden('#skF_1'('#skF_2',B_101,'#skF_4'),B_101)
      | ~ m1_orders_2('#skF_4','#skF_2',B_101)
      | k1_xboole_0 = B_101
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_351])).

tff(c_404,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_398])).

tff(c_411,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_404])).

tff(c_412,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_411])).

tff(c_26,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_344,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_1'('#skF_2',B_94,'#skF_3'),B_94)
      | ~ m1_orders_2('#skF_3','#skF_2',B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_338])).

tff(c_355,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_1'('#skF_2',B_94,'#skF_3'),B_94)
      | ~ m1_orders_2('#skF_3','#skF_2',B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_344])).

tff(c_366,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_2',B_96,'#skF_3'),B_96)
      | ~ m1_orders_2('#skF_3','#skF_2',B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_355])).

tff(c_370,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_366])).

tff(c_376,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_370])).

tff(c_380,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_124,plain,(
    ! [A_74,B_75,C_76] :
      ( k3_orders_2(A_74,B_75,'#skF_1'(A_74,B_75,C_76)) = C_76
      | ~ m1_orders_2(C_76,A_74,B_75)
      | k1_xboole_0 = B_75
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [B_75] :
      ( k3_orders_2('#skF_2',B_75,'#skF_1'('#skF_2',B_75,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_75)
      | k1_xboole_0 = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_131,plain,(
    ! [B_75] :
      ( k3_orders_2('#skF_2',B_75,'#skF_1'('#skF_2',B_75,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_75)
      | k1_xboole_0 = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_126])).

tff(c_137,plain,(
    ! [B_77] :
      ( k3_orders_2('#skF_2',B_77,'#skF_1'('#skF_2',B_77,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_131])).

tff(c_141,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_137])).

tff(c_146,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_141])).

tff(c_147,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_146])).

tff(c_152,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_20])).

tff(c_159,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_152])).

tff(c_160,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_159])).

tff(c_175,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_178,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_175])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_30,c_24,c_178])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_28,c_181])).

tff(c_185,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_72,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_1'(A_58,B_59,C_60),B_59)
      | ~ m1_orders_2(C_60,A_58,B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_orders_2(A_58)
      | ~ v5_orders_2(A_58)
      | ~ v4_orders_2(A_58)
      | ~ v3_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_2',B_59,'#skF_4'),B_59)
      | ~ m1_orders_2('#skF_4','#skF_2',B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_79,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_2',B_59,'#skF_4'),B_59)
      | ~ m1_orders_2('#skF_4','#skF_2',B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_74])).

tff(c_85,plain,(
    ! [B_61] :
      ( r2_hidden('#skF_1'('#skF_2',B_61,'#skF_4'),B_61)
      | ~ m1_orders_2('#skF_4','#skF_2',B_61)
      | k1_xboole_0 = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_79])).

tff(c_89,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_93,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_89])).

tff(c_94,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_93])).

tff(c_76,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_2',B_59,'#skF_3'),B_59)
      | ~ m1_orders_2('#skF_3','#skF_2',B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_83,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_2',B_59,'#skF_3'),B_59)
      | ~ m1_orders_2('#skF_3','#skF_2',B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_76])).

tff(c_96,plain,(
    ! [B_62] :
      ( r2_hidden('#skF_1'('#skF_2',B_62,'#skF_3'),B_62)
      | ~ m1_orders_2('#skF_3','#skF_2',B_62)
      | k1_xboole_0 = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_83])).

tff(c_98,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_96])).

tff(c_103,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_98])).

tff(c_107,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_58,plain,(
    ! [C_56,A_57] :
      ( k1_xboole_0 = C_56
      | ~ m1_orders_2(C_56,A_57,k1_xboole_0)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_69,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_62])).

tff(c_70,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_28,c_69])).

tff(c_71,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_71])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_110])).

tff(c_119,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_128,plain,(
    ! [B_75] :
      ( k3_orders_2('#skF_2',B_75,'#skF_1'('#skF_2',B_75,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_75)
      | k1_xboole_0 = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_124])).

tff(c_135,plain,(
    ! [B_75] :
      ( k3_orders_2('#skF_2',B_75,'#skF_1'('#skF_2',B_75,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_75)
      | k1_xboole_0 = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_128])).

tff(c_186,plain,(
    ! [B_82] :
      ( k3_orders_2('#skF_2',B_82,'#skF_1'('#skF_2',B_82,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_82)
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_135])).

tff(c_188,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_193,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_188])).

tff(c_194,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_193])).

tff(c_201,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_20])).

tff(c_208,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_30,c_201])).

tff(c_209,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_208])).

tff(c_225,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_228,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_30,c_32,c_26,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_119,c_231])).

tff(c_253,plain,(
    ! [B_87] :
      ( r2_hidden(B_87,'#skF_4')
      | ~ r2_hidden(B_87,'#skF_3')
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_259,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_253])).

tff(c_269,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_259])).

tff(c_22,plain,(
    ! [A_30,B_38,C_42,D_44] :
      ( r2_orders_2(A_30,B_38,C_42)
      | ~ r2_hidden(B_38,k3_orders_2(A_30,D_44,C_42))
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(C_42,u1_struct_0(A_30))
      | ~ m1_subset_1(B_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_150,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_22])).

tff(c_156,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_150])).

tff(c_157,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_156])).

tff(c_312,plain,(
    ! [B_92] :
      ( r2_orders_2('#skF_2',B_92,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_92,'#skF_4')
      | ~ m1_subset_1(B_92,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_157])).

tff(c_16,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r2_orders_2(A_27,B_28,B_28)
      | ~ m1_subset_1(C_29,u1_struct_0(A_27))
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_315,plain,(
    ! [C_29] :
      ( ~ m1_subset_1(C_29,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_312,c_16])).

tff(c_318,plain,(
    ! [C_29] : ~ m1_subset_1(C_29,u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_269,c_34,c_315])).

tff(c_235,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_318,c_235])).

tff(c_322,plain,(
    ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_386,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_322])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_386])).

tff(c_395,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_441,plain,(
    ! [B_111] :
      ( k3_orders_2('#skF_2',B_111,'#skF_1'('#skF_2',B_111,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_435])).

tff(c_452,plain,(
    ! [B_111] :
      ( k3_orders_2('#skF_2',B_111,'#skF_1'('#skF_2',B_111,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_441])).

tff(c_526,plain,(
    ! [B_119] :
      ( k3_orders_2('#skF_2',B_119,'#skF_1'('#skF_2',B_119,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_119)
      | k1_xboole_0 = B_119
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_452])).

tff(c_530,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_526])).

tff(c_536,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_530])).

tff(c_537,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_536])).

tff(c_544,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_20])).

tff(c_551,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_30,c_544])).

tff(c_552,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_551])).

tff(c_554,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_552])).

tff(c_572,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_554])).

tff(c_575,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_30,c_32,c_26,c_572])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_395,c_575])).

tff(c_586,plain,(
    ! [B_121] :
      ( r2_hidden(B_121,'#skF_4')
      | ~ r2_hidden(B_121,'#skF_3')
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_592,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_492,c_586])).

tff(c_602,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_592])).

tff(c_470,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_22])).

tff(c_476,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_470])).

tff(c_477,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_476])).

tff(c_684,plain,(
    ! [B_132] :
      ( r2_orders_2('#skF_2',B_132,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_132,'#skF_4')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_477])).

tff(c_687,plain,(
    ! [C_29] :
      ( ~ m1_subset_1(C_29,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_684,c_16])).

tff(c_690,plain,(
    ! [C_29] : ~ m1_subset_1(C_29,u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_602,c_34,c_687])).

tff(c_579,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_690,c_579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.53  
% 3.25/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.53  %$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.25/1.53  
% 3.25/1.53  %Foreground sorts:
% 3.25/1.53  
% 3.25/1.53  
% 3.25/1.53  %Background operators:
% 3.25/1.53  
% 3.25/1.53  
% 3.25/1.53  %Foreground operators:
% 3.25/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.25/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.25/1.53  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.53  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.25/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.53  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.25/1.53  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.25/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.53  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.53  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.25/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.53  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.25/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.25/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.53  
% 3.37/1.56  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.37/1.56  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 3.37/1.56  tff(f_113, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.37/1.56  tff(f_87, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => ~r2_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_orders_2)).
% 3.37/1.56  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_40, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_38, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_36, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_34, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_24, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_12, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.37/1.56  tff(c_435, plain, (![A_110, B_111, C_112]: (k3_orders_2(A_110, B_111, '#skF_1'(A_110, B_111, C_112))=C_112 | ~m1_orders_2(C_112, A_110, B_111) | k1_xboole_0=B_111 | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.37/1.56  tff(c_439, plain, (![B_111]: (k3_orders_2('#skF_2', B_111, '#skF_1'('#skF_2', B_111, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_435])).
% 3.37/1.56  tff(c_448, plain, (![B_111]: (k3_orders_2('#skF_2', B_111, '#skF_1'('#skF_2', B_111, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_439])).
% 3.37/1.56  tff(c_454, plain, (![B_113]: (k3_orders_2('#skF_2', B_113, '#skF_1'('#skF_2', B_113, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_113) | k1_xboole_0=B_113 | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_448])).
% 3.37/1.56  tff(c_460, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_454])).
% 3.37/1.56  tff(c_466, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_460])).
% 3.37/1.56  tff(c_467, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_466])).
% 3.37/1.56  tff(c_20, plain, (![B_38, D_44, A_30, C_42]: (r2_hidden(B_38, D_44) | ~r2_hidden(B_38, k3_orders_2(A_30, D_44, C_42)) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.37/1.56  tff(c_472, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_467, c_20])).
% 3.37/1.56  tff(c_479, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_472])).
% 3.37/1.56  tff(c_480, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_479])).
% 3.37/1.56  tff(c_482, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_480])).
% 3.37/1.56  tff(c_485, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_482])).
% 3.37/1.56  tff(c_488, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_30, c_24, c_485])).
% 3.37/1.56  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_28, c_488])).
% 3.37/1.56  tff(c_492, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_480])).
% 3.37/1.56  tff(c_338, plain, (![A_93, B_94, C_95]: (r2_hidden('#skF_1'(A_93, B_94, C_95), B_94) | ~m1_orders_2(C_95, A_93, B_94) | k1_xboole_0=B_94 | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.37/1.56  tff(c_342, plain, (![B_94]: (r2_hidden('#skF_1'('#skF_2', B_94, '#skF_4'), B_94) | ~m1_orders_2('#skF_4', '#skF_2', B_94) | k1_xboole_0=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_338])).
% 3.37/1.56  tff(c_351, plain, (![B_94]: (r2_hidden('#skF_1'('#skF_2', B_94, '#skF_4'), B_94) | ~m1_orders_2('#skF_4', '#skF_2', B_94) | k1_xboole_0=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_342])).
% 3.37/1.56  tff(c_398, plain, (![B_101]: (r2_hidden('#skF_1'('#skF_2', B_101, '#skF_4'), B_101) | ~m1_orders_2('#skF_4', '#skF_2', B_101) | k1_xboole_0=B_101 | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_351])).
% 3.37/1.56  tff(c_404, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_398])).
% 3.37/1.56  tff(c_411, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_404])).
% 3.37/1.56  tff(c_412, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_411])).
% 3.37/1.56  tff(c_26, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.37/1.56  tff(c_344, plain, (![B_94]: (r2_hidden('#skF_1'('#skF_2', B_94, '#skF_3'), B_94) | ~m1_orders_2('#skF_3', '#skF_2', B_94) | k1_xboole_0=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_338])).
% 3.37/1.56  tff(c_355, plain, (![B_94]: (r2_hidden('#skF_1'('#skF_2', B_94, '#skF_3'), B_94) | ~m1_orders_2('#skF_3', '#skF_2', B_94) | k1_xboole_0=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_344])).
% 3.37/1.56  tff(c_366, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_2', B_96, '#skF_3'), B_96) | ~m1_orders_2('#skF_3', '#skF_2', B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_355])).
% 3.37/1.56  tff(c_370, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_366])).
% 3.37/1.56  tff(c_376, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_370])).
% 3.37/1.56  tff(c_380, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_376])).
% 3.37/1.56  tff(c_124, plain, (![A_74, B_75, C_76]: (k3_orders_2(A_74, B_75, '#skF_1'(A_74, B_75, C_76))=C_76 | ~m1_orders_2(C_76, A_74, B_75) | k1_xboole_0=B_75 | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.37/1.56  tff(c_126, plain, (![B_75]: (k3_orders_2('#skF_2', B_75, '#skF_1'('#skF_2', B_75, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_75) | k1_xboole_0=B_75 | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_124])).
% 3.37/1.56  tff(c_131, plain, (![B_75]: (k3_orders_2('#skF_2', B_75, '#skF_1'('#skF_2', B_75, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_75) | k1_xboole_0=B_75 | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_126])).
% 3.37/1.56  tff(c_137, plain, (![B_77]: (k3_orders_2('#skF_2', B_77, '#skF_1'('#skF_2', B_77, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_77) | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_131])).
% 3.37/1.56  tff(c_141, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_137])).
% 3.37/1.56  tff(c_146, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_141])).
% 3.37/1.56  tff(c_147, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_146])).
% 3.37/1.56  tff(c_152, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_20])).
% 3.37/1.56  tff(c_159, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_152])).
% 3.37/1.56  tff(c_160, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_159])).
% 3.37/1.56  tff(c_175, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_160])).
% 3.37/1.56  tff(c_178, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_175])).
% 3.37/1.56  tff(c_181, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_30, c_24, c_178])).
% 3.37/1.56  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_28, c_181])).
% 3.37/1.56  tff(c_185, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_160])).
% 3.37/1.56  tff(c_72, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_1'(A_58, B_59, C_60), B_59) | ~m1_orders_2(C_60, A_58, B_59) | k1_xboole_0=B_59 | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_orders_2(A_58) | ~v5_orders_2(A_58) | ~v4_orders_2(A_58) | ~v3_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.37/1.56  tff(c_74, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_2', B_59, '#skF_4'), B_59) | ~m1_orders_2('#skF_4', '#skF_2', B_59) | k1_xboole_0=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_72])).
% 3.37/1.56  tff(c_79, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_2', B_59, '#skF_4'), B_59) | ~m1_orders_2('#skF_4', '#skF_2', B_59) | k1_xboole_0=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_74])).
% 3.37/1.56  tff(c_85, plain, (![B_61]: (r2_hidden('#skF_1'('#skF_2', B_61, '#skF_4'), B_61) | ~m1_orders_2('#skF_4', '#skF_2', B_61) | k1_xboole_0=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_79])).
% 3.37/1.56  tff(c_89, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_85])).
% 3.37/1.56  tff(c_93, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_89])).
% 3.37/1.56  tff(c_94, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_93])).
% 3.37/1.56  tff(c_76, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_2', B_59, '#skF_3'), B_59) | ~m1_orders_2('#skF_3', '#skF_2', B_59) | k1_xboole_0=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_72])).
% 3.37/1.56  tff(c_83, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_2', B_59, '#skF_3'), B_59) | ~m1_orders_2('#skF_3', '#skF_2', B_59) | k1_xboole_0=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_76])).
% 3.37/1.56  tff(c_96, plain, (![B_62]: (r2_hidden('#skF_1'('#skF_2', B_62, '#skF_3'), B_62) | ~m1_orders_2('#skF_3', '#skF_2', B_62) | k1_xboole_0=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_83])).
% 3.37/1.56  tff(c_98, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_96])).
% 3.37/1.56  tff(c_103, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_98])).
% 3.37/1.56  tff(c_107, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_103])).
% 3.37/1.56  tff(c_58, plain, (![C_56, A_57]: (k1_xboole_0=C_56 | ~m1_orders_2(C_56, A_57, k1_xboole_0) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.37/1.56  tff(c_62, plain, (k1_xboole_0='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_58])).
% 3.37/1.56  tff(c_69, plain, (k1_xboole_0='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_62])).
% 3.37/1.56  tff(c_70, plain, (~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_28, c_69])).
% 3.37/1.56  tff(c_71, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_70])).
% 3.37/1.56  tff(c_110, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_71])).
% 3.37/1.56  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_110])).
% 3.37/1.56  tff(c_119, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_103])).
% 3.37/1.56  tff(c_128, plain, (![B_75]: (k3_orders_2('#skF_2', B_75, '#skF_1'('#skF_2', B_75, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_75) | k1_xboole_0=B_75 | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_124])).
% 3.37/1.56  tff(c_135, plain, (![B_75]: (k3_orders_2('#skF_2', B_75, '#skF_1'('#skF_2', B_75, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_75) | k1_xboole_0=B_75 | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_128])).
% 3.37/1.56  tff(c_186, plain, (![B_82]: (k3_orders_2('#skF_2', B_82, '#skF_1'('#skF_2', B_82, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_82) | k1_xboole_0=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_135])).
% 3.37/1.56  tff(c_188, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_186])).
% 3.37/1.56  tff(c_193, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_188])).
% 3.37/1.56  tff(c_194, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_119, c_193])).
% 3.37/1.56  tff(c_201, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_20])).
% 3.37/1.56  tff(c_208, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_30, c_201])).
% 3.37/1.56  tff(c_209, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_208])).
% 3.37/1.56  tff(c_225, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_209])).
% 3.37/1.56  tff(c_228, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_225])).
% 3.37/1.56  tff(c_231, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_30, c_32, c_26, c_228])).
% 3.37/1.56  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_119, c_231])).
% 3.37/1.56  tff(c_253, plain, (![B_87]: (r2_hidden(B_87, '#skF_4') | ~r2_hidden(B_87, '#skF_3') | ~m1_subset_1(B_87, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_209])).
% 3.37/1.56  tff(c_259, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_185, c_253])).
% 3.37/1.56  tff(c_269, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_259])).
% 3.37/1.56  tff(c_22, plain, (![A_30, B_38, C_42, D_44]: (r2_orders_2(A_30, B_38, C_42) | ~r2_hidden(B_38, k3_orders_2(A_30, D_44, C_42)) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.37/1.56  tff(c_150, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_22])).
% 3.37/1.56  tff(c_156, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_150])).
% 3.37/1.56  tff(c_157, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_156])).
% 3.37/1.56  tff(c_312, plain, (![B_92]: (r2_orders_2('#skF_2', B_92, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_92, '#skF_4') | ~m1_subset_1(B_92, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_157])).
% 3.37/1.56  tff(c_16, plain, (![A_27, B_28, C_29]: (~r2_orders_2(A_27, B_28, B_28) | ~m1_subset_1(C_29, u1_struct_0(A_27)) | ~m1_subset_1(B_28, u1_struct_0(A_27)) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.37/1.56  tff(c_315, plain, (![C_29]: (~m1_subset_1(C_29, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_312, c_16])).
% 3.37/1.56  tff(c_318, plain, (![C_29]: (~m1_subset_1(C_29, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_269, c_34, c_315])).
% 3.37/1.56  tff(c_235, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_209])).
% 3.37/1.56  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_318, c_235])).
% 3.37/1.56  tff(c_322, plain, (~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_70])).
% 3.37/1.56  tff(c_386, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_322])).
% 3.37/1.56  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_386])).
% 3.37/1.56  tff(c_395, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_376])).
% 3.37/1.56  tff(c_441, plain, (![B_111]: (k3_orders_2('#skF_2', B_111, '#skF_1'('#skF_2', B_111, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_435])).
% 3.37/1.56  tff(c_452, plain, (![B_111]: (k3_orders_2('#skF_2', B_111, '#skF_1'('#skF_2', B_111, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_441])).
% 3.37/1.56  tff(c_526, plain, (![B_119]: (k3_orders_2('#skF_2', B_119, '#skF_1'('#skF_2', B_119, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_119) | k1_xboole_0=B_119 | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_452])).
% 3.37/1.56  tff(c_530, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_526])).
% 3.37/1.56  tff(c_536, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_530])).
% 3.37/1.56  tff(c_537, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_395, c_536])).
% 3.37/1.56  tff(c_544, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_20])).
% 3.37/1.56  tff(c_551, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_30, c_544])).
% 3.37/1.56  tff(c_552, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_551])).
% 3.37/1.56  tff(c_554, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_552])).
% 3.37/1.56  tff(c_572, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_554])).
% 3.37/1.56  tff(c_575, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_30, c_32, c_26, c_572])).
% 3.37/1.56  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_395, c_575])).
% 3.37/1.56  tff(c_586, plain, (![B_121]: (r2_hidden(B_121, '#skF_4') | ~r2_hidden(B_121, '#skF_3') | ~m1_subset_1(B_121, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_552])).
% 3.37/1.56  tff(c_592, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_492, c_586])).
% 3.37/1.56  tff(c_602, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_412, c_592])).
% 3.37/1.56  tff(c_470, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_467, c_22])).
% 3.37/1.56  tff(c_476, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_470])).
% 3.37/1.56  tff(c_477, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_476])).
% 3.37/1.56  tff(c_684, plain, (![B_132]: (r2_orders_2('#skF_2', B_132, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_132, '#skF_4') | ~m1_subset_1(B_132, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_477])).
% 3.37/1.56  tff(c_687, plain, (![C_29]: (~m1_subset_1(C_29, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_684, c_16])).
% 3.37/1.56  tff(c_690, plain, (![C_29]: (~m1_subset_1(C_29, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_602, c_34, c_687])).
% 3.37/1.56  tff(c_579, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_552])).
% 3.37/1.56  tff(c_693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_690, c_579])).
% 3.37/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.56  
% 3.37/1.56  Inference rules
% 3.37/1.56  ----------------------
% 3.37/1.56  #Ref     : 0
% 3.37/1.56  #Sup     : 103
% 3.37/1.56  #Fact    : 0
% 3.37/1.56  #Define  : 0
% 3.37/1.56  #Split   : 14
% 3.37/1.56  #Chain   : 0
% 3.37/1.56  #Close   : 0
% 3.37/1.56  
% 3.37/1.56  Ordering : KBO
% 3.37/1.56  
% 3.37/1.56  Simplification rules
% 3.37/1.56  ----------------------
% 3.37/1.56  #Subsume      : 28
% 3.37/1.56  #Demod        : 331
% 3.37/1.56  #Tautology    : 34
% 3.37/1.56  #SimpNegUnit  : 75
% 3.37/1.56  #BackRed      : 20
% 3.37/1.56  
% 3.37/1.56  #Partial instantiations: 0
% 3.37/1.56  #Strategies tried      : 1
% 3.37/1.56  
% 3.37/1.56  Timing (in seconds)
% 3.37/1.56  ----------------------
% 3.37/1.56  Preprocessing        : 0.35
% 3.37/1.56  Parsing              : 0.18
% 3.37/1.56  CNF conversion       : 0.03
% 3.37/1.56  Main loop            : 0.36
% 3.37/1.56  Inferencing          : 0.12
% 3.37/1.56  Reduction            : 0.13
% 3.37/1.56  Demodulation         : 0.09
% 3.37/1.56  BG Simplification    : 0.02
% 3.37/1.56  Subsumption          : 0.07
% 3.37/1.56  Abstraction          : 0.02
% 3.37/1.56  MUC search           : 0.00
% 3.37/1.56  Cooper               : 0.00
% 3.37/1.56  Total                : 0.76
% 3.37/1.56  Index Insertion      : 0.00
% 3.37/1.56  Index Deletion       : 0.00
% 3.37/1.56  Index Matching       : 0.00
% 3.37/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
