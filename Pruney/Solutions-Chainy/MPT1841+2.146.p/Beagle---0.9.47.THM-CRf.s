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
% DateTime   : Thu Dec  3 10:28:47 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 139 expanded)
%              Number of leaves         :   44 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  108 ( 239 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_38,plain,(
    ! [A_28] : l1_orders_2(k2_yellow_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_205,plain,(
    ! [A_78,B_79] :
      ( k6_domain_1(A_78,B_79) = k1_tarski(B_79)
      | ~ m1_subset_1(B_79,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_211,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_205])).

tff(c_215,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_211])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k6_domain_1(A_23,B_24),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_229,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_30])).

tff(c_233,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_229])).

tff(c_234,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_233])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_243,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_234,c_22])).

tff(c_273,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(A_85,B_84)
      | ~ v1_zfmisc_1(B_84)
      | v1_xboole_0(B_84)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_279,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_243,c_273])).

tff(c_289,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_279])).

tff(c_290,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_289])).

tff(c_294,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_146,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_2'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [A_70,B_71] :
      ( ~ v1_xboole_0(A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_186,plain,(
    ! [A_70,B_71] :
      ( k2_xboole_0(A_70,B_71) = B_71
      | ~ v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_182,c_14])).

tff(c_312,plain,(
    ! [B_89] : k2_xboole_0(k1_tarski('#skF_4'),B_89) = B_89 ),
    inference(resolution,[status(thm)],[c_294,c_186])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_321,plain,(
    ! [B_89] : k1_xboole_0 != B_89 ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_20])).

tff(c_336,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_321])).

tff(c_337,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_48,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_225,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_48])).

tff(c_342,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_225])).

tff(c_40,plain,(
    ! [A_29] : u1_struct_0(k2_yellow_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_90,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_98,plain,(
    ! [A_28] : u1_struct_0(k2_yellow_1(A_28)) = k2_struct_0(k2_yellow_1(A_28)) ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_100,plain,(
    ! [A_28] : k2_struct_0(k2_yellow_1(A_28)) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98])).

tff(c_112,plain,(
    ! [A_52] :
      ( ~ v1_subset_1(k2_struct_0(A_52),u1_struct_0(A_52))
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_118,plain,(
    ! [A_29] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_29)),A_29)
      | ~ l1_struct_0(k2_yellow_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_112])).

tff(c_120,plain,(
    ! [A_29] :
      ( ~ v1_subset_1(A_29,A_29)
      | ~ l1_struct_0(k2_yellow_1(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_118])).

tff(c_357,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_342,c_120])).

tff(c_360,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_357])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:30:55 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.73  
% 2.81/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.73  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.81/1.73  
% 2.81/1.73  %Foreground sorts:
% 2.81/1.73  
% 2.81/1.73  
% 2.81/1.73  %Background operators:
% 2.81/1.73  
% 2.81/1.73  
% 2.81/1.73  %Foreground operators:
% 2.81/1.73  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.81/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.73  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.81/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.73  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.81/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.73  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.81/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.73  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.81/1.73  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.81/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.73  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.73  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.81/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.73  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.81/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.73  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.81/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.73  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.81/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.73  
% 2.81/1.75  tff(f_86, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.81/1.75  tff(f_75, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.81/1.75  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.81/1.75  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.81/1.75  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.81/1.75  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.81/1.75  tff(f_103, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.81/1.75  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.81/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.81/1.75  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.81/1.75  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.81/1.75  tff(f_90, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.81/1.75  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.81/1.75  tff(f_64, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.81/1.75  tff(c_38, plain, (![A_28]: (l1_orders_2(k2_yellow_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.75  tff(c_32, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.81/1.75  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.81/1.75  tff(c_46, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.81/1.75  tff(c_50, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.81/1.75  tff(c_205, plain, (![A_78, B_79]: (k6_domain_1(A_78, B_79)=k1_tarski(B_79) | ~m1_subset_1(B_79, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.81/1.75  tff(c_211, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_205])).
% 2.81/1.75  tff(c_215, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_211])).
% 2.81/1.75  tff(c_30, plain, (![A_23, B_24]: (m1_subset_1(k6_domain_1(A_23, B_24), k1_zfmisc_1(A_23)) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.75  tff(c_229, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_215, c_30])).
% 2.81/1.75  tff(c_233, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_229])).
% 2.81/1.75  tff(c_234, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_233])).
% 2.81/1.75  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.81/1.75  tff(c_243, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_234, c_22])).
% 2.81/1.75  tff(c_273, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(A_85, B_84) | ~v1_zfmisc_1(B_84) | v1_xboole_0(B_84) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.81/1.75  tff(c_279, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_243, c_273])).
% 2.81/1.75  tff(c_289, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_279])).
% 2.81/1.75  tff(c_290, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_289])).
% 2.81/1.75  tff(c_294, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_290])).
% 2.81/1.75  tff(c_146, plain, (![A_62, B_63]: (r2_hidden('#skF_2'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.75  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.75  tff(c_182, plain, (![A_70, B_71]: (~v1_xboole_0(A_70) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_146, c_2])).
% 2.81/1.75  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.81/1.75  tff(c_186, plain, (![A_70, B_71]: (k2_xboole_0(A_70, B_71)=B_71 | ~v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_182, c_14])).
% 2.81/1.75  tff(c_312, plain, (![B_89]: (k2_xboole_0(k1_tarski('#skF_4'), B_89)=B_89)), inference(resolution, [status(thm)], [c_294, c_186])).
% 2.81/1.75  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.75  tff(c_321, plain, (![B_89]: (k1_xboole_0!=B_89)), inference(superposition, [status(thm), theory('equality')], [c_312, c_20])).
% 2.81/1.75  tff(c_336, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_321])).
% 2.81/1.75  tff(c_337, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_290])).
% 2.81/1.75  tff(c_48, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.81/1.75  tff(c_225, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_48])).
% 2.81/1.75  tff(c_342, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_225])).
% 2.81/1.75  tff(c_40, plain, (![A_29]: (u1_struct_0(k2_yellow_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.81/1.75  tff(c_90, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.81/1.75  tff(c_95, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_32, c_90])).
% 2.81/1.75  tff(c_98, plain, (![A_28]: (u1_struct_0(k2_yellow_1(A_28))=k2_struct_0(k2_yellow_1(A_28)))), inference(resolution, [status(thm)], [c_38, c_95])).
% 2.81/1.75  tff(c_100, plain, (![A_28]: (k2_struct_0(k2_yellow_1(A_28))=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98])).
% 2.81/1.75  tff(c_112, plain, (![A_52]: (~v1_subset_1(k2_struct_0(A_52), u1_struct_0(A_52)) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.75  tff(c_118, plain, (![A_29]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_29)), A_29) | ~l1_struct_0(k2_yellow_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_112])).
% 2.81/1.75  tff(c_120, plain, (![A_29]: (~v1_subset_1(A_29, A_29) | ~l1_struct_0(k2_yellow_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_118])).
% 2.81/1.75  tff(c_357, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_342, c_120])).
% 2.81/1.75  tff(c_360, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_357])).
% 2.81/1.75  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_360])).
% 2.81/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.75  
% 2.81/1.75  Inference rules
% 2.81/1.75  ----------------------
% 2.81/1.75  #Ref     : 1
% 2.81/1.75  #Sup     : 67
% 2.81/1.75  #Fact    : 0
% 2.81/1.75  #Define  : 0
% 2.81/1.75  #Split   : 1
% 2.81/1.75  #Chain   : 0
% 2.81/1.75  #Close   : 0
% 2.81/1.75  
% 2.81/1.75  Ordering : KBO
% 2.81/1.75  
% 2.81/1.75  Simplification rules
% 2.81/1.75  ----------------------
% 2.81/1.75  #Subsume      : 7
% 2.81/1.75  #Demod        : 18
% 2.81/1.75  #Tautology    : 36
% 2.81/1.75  #SimpNegUnit  : 4
% 2.81/1.75  #BackRed      : 6
% 2.81/1.75  
% 2.81/1.75  #Partial instantiations: 0
% 2.81/1.75  #Strategies tried      : 1
% 2.81/1.75  
% 2.81/1.75  Timing (in seconds)
% 2.81/1.75  ----------------------
% 2.81/1.75  Preprocessing        : 0.52
% 2.81/1.75  Parsing              : 0.28
% 2.81/1.75  CNF conversion       : 0.04
% 2.81/1.75  Main loop            : 0.32
% 2.81/1.75  Inferencing          : 0.13
% 2.81/1.75  Reduction            : 0.09
% 2.81/1.75  Demodulation         : 0.07
% 2.81/1.75  BG Simplification    : 0.02
% 2.81/1.75  Subsumption          : 0.04
% 2.81/1.75  Abstraction          : 0.02
% 2.81/1.75  MUC search           : 0.00
% 2.81/1.75  Cooper               : 0.00
% 2.81/1.75  Total                : 0.88
% 2.81/1.75  Index Insertion      : 0.00
% 2.81/1.75  Index Deletion       : 0.00
% 2.81/1.75  Index Matching       : 0.00
% 2.81/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
