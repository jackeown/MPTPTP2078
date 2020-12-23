%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:45 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 148 expanded)
%              Number of leaves         :   44 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 263 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
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
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_95,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_42,plain,(
    ! [A_27] : l1_orders_2(k2_yellow_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,(
    ! [A_41,B_42] : k2_xboole_0(k1_tarski(A_41),B_42) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [A_41] : k1_tarski(A_41) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_228,plain,(
    ! [A_80,B_81] :
      ( k6_domain_1(A_80,B_81) = k1_tarski(B_81)
      | ~ m1_subset_1(B_81,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_234,plain,
    ( k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_228])).

tff(c_238,plain,(
    k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_234])).

tff(c_268,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k6_domain_1(A_86,B_87),k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_279,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_268])).

tff(c_284,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279])).

tff(c_285,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_284])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_296,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_285,c_24])).

tff(c_48,plain,(
    ! [B_31,A_29] :
      ( B_31 = A_29
      | ~ r1_tarski(A_29,B_31)
      | ~ v1_zfmisc_1(B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_299,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_296,c_48])).

tff(c_309,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_299])).

tff(c_310,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_309])).

tff(c_341,plain,(
    v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_185,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_189,plain,(
    ! [B_69,A_70,A_71] :
      ( ~ v1_xboole_0(B_69)
      | ~ r2_hidden(A_70,A_71)
      | ~ r1_tarski(A_71,B_69) ) ),
    inference(resolution,[status(thm)],[c_26,c_185])).

tff(c_193,plain,(
    ! [B_72,A_73,B_74] :
      ( ~ v1_xboole_0(B_72)
      | ~ r1_tarski(A_73,B_72)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_189])).

tff(c_201,plain,(
    ! [B_75,B_76] :
      ( ~ v1_xboole_0(B_75)
      | r1_tarski(B_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_151,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_211,plain,(
    ! [B_75] :
      ( k1_xboole_0 = B_75
      | ~ v1_xboole_0(B_75) ) ),
    inference(resolution,[status(thm)],[c_201,c_151])).

tff(c_346,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_341,c_211])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_346])).

tff(c_352,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_52,plain,(
    v1_subset_1(k6_domain_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_239,plain,(
    v1_subset_1(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_52])).

tff(c_356,plain,(
    v1_subset_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_239])).

tff(c_44,plain,(
    ! [A_28] : u1_struct_0(k2_yellow_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_105,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_36,c_105])).

tff(c_113,plain,(
    ! [A_27] : u1_struct_0(k2_yellow_1(A_27)) = k2_struct_0(k2_yellow_1(A_27)) ),
    inference(resolution,[status(thm)],[c_42,c_110])).

tff(c_115,plain,(
    ! [A_27] : k2_struct_0(k2_yellow_1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113])).

tff(c_131,plain,(
    ! [A_52] :
      ( ~ v1_subset_1(k2_struct_0(A_52),u1_struct_0(A_52))
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_137,plain,(
    ! [A_28] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_28)),A_28)
      | ~ l1_struct_0(k2_yellow_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_131])).

tff(c_139,plain,(
    ! [A_28] :
      ( ~ v1_subset_1(A_28,A_28)
      | ~ l1_struct_0(k2_yellow_1(A_28)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_137])).

tff(c_369,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_356,c_139])).

tff(c_373,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_369])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.30  
% 2.37/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.30  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.37/1.30  
% 2.37/1.30  %Foreground sorts:
% 2.37/1.30  
% 2.37/1.30  
% 2.37/1.30  %Background operators:
% 2.37/1.30  
% 2.37/1.30  
% 2.37/1.30  %Foreground operators:
% 2.37/1.30  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.37/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.30  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.37/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.30  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.37/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.37/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.37/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.37/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.37/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.30  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.37/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.30  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.37/1.30  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.37/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.37/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.30  
% 2.37/1.32  tff(f_91, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.37/1.32  tff(f_80, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.37/1.32  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.37/1.32  tff(f_49, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.37/1.32  tff(f_120, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.37/1.32  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.37/1.32  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.37/1.32  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.37/1.32  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.37/1.32  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.37/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.37/1.32  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.37/1.32  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.37/1.32  tff(f_95, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.37/1.32  tff(f_64, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.37/1.32  tff(f_69, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.37/1.32  tff(c_42, plain, (![A_27]: (l1_orders_2(k2_yellow_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.37/1.32  tff(c_36, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.37/1.32  tff(c_14, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.37/1.32  tff(c_90, plain, (![A_41, B_42]: (k2_xboole_0(k1_tarski(A_41), B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.37/1.32  tff(c_94, plain, (![A_41]: (k1_tarski(A_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_90])).
% 2.37/1.32  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.37/1.32  tff(c_50, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.37/1.32  tff(c_54, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.37/1.32  tff(c_228, plain, (![A_80, B_81]: (k6_domain_1(A_80, B_81)=k1_tarski(B_81) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.37/1.32  tff(c_234, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_228])).
% 2.37/1.32  tff(c_238, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_234])).
% 2.37/1.32  tff(c_268, plain, (![A_86, B_87]: (m1_subset_1(k6_domain_1(A_86, B_87), k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.37/1.32  tff(c_279, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_238, c_268])).
% 2.37/1.32  tff(c_284, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279])).
% 2.37/1.32  tff(c_285, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_284])).
% 2.37/1.32  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.37/1.32  tff(c_296, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_285, c_24])).
% 2.37/1.32  tff(c_48, plain, (![B_31, A_29]: (B_31=A_29 | ~r1_tarski(A_29, B_31) | ~v1_zfmisc_1(B_31) | v1_xboole_0(B_31) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.37/1.32  tff(c_299, plain, (k1_tarski('#skF_3')='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_296, c_48])).
% 2.37/1.32  tff(c_309, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_299])).
% 2.37/1.32  tff(c_310, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0(k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_309])).
% 2.37/1.32  tff(c_341, plain, (v1_xboole_0(k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_310])).
% 2.37/1.32  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.32  tff(c_26, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.37/1.32  tff(c_185, plain, (![C_66, B_67, A_68]: (~v1_xboole_0(C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.37/1.32  tff(c_189, plain, (![B_69, A_70, A_71]: (~v1_xboole_0(B_69) | ~r2_hidden(A_70, A_71) | ~r1_tarski(A_71, B_69))), inference(resolution, [status(thm)], [c_26, c_185])).
% 2.37/1.32  tff(c_193, plain, (![B_72, A_73, B_74]: (~v1_xboole_0(B_72) | ~r1_tarski(A_73, B_72) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_6, c_189])).
% 2.37/1.32  tff(c_201, plain, (![B_75, B_76]: (~v1_xboole_0(B_75) | r1_tarski(B_75, B_76))), inference(resolution, [status(thm)], [c_12, c_193])).
% 2.37/1.32  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.37/1.32  tff(c_142, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.32  tff(c_151, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_142])).
% 2.37/1.32  tff(c_211, plain, (![B_75]: (k1_xboole_0=B_75 | ~v1_xboole_0(B_75))), inference(resolution, [status(thm)], [c_201, c_151])).
% 2.37/1.32  tff(c_346, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_341, c_211])).
% 2.37/1.32  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_346])).
% 2.37/1.32  tff(c_352, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_310])).
% 2.37/1.32  tff(c_52, plain, (v1_subset_1(k6_domain_1('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.37/1.32  tff(c_239, plain, (v1_subset_1(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_52])).
% 2.37/1.32  tff(c_356, plain, (v1_subset_1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_239])).
% 2.37/1.32  tff(c_44, plain, (![A_28]: (u1_struct_0(k2_yellow_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.37/1.32  tff(c_105, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.32  tff(c_110, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_36, c_105])).
% 2.37/1.32  tff(c_113, plain, (![A_27]: (u1_struct_0(k2_yellow_1(A_27))=k2_struct_0(k2_yellow_1(A_27)))), inference(resolution, [status(thm)], [c_42, c_110])).
% 2.37/1.32  tff(c_115, plain, (![A_27]: (k2_struct_0(k2_yellow_1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113])).
% 2.37/1.32  tff(c_131, plain, (![A_52]: (~v1_subset_1(k2_struct_0(A_52), u1_struct_0(A_52)) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.32  tff(c_137, plain, (![A_28]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_28)), A_28) | ~l1_struct_0(k2_yellow_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_131])).
% 2.37/1.32  tff(c_139, plain, (![A_28]: (~v1_subset_1(A_28, A_28) | ~l1_struct_0(k2_yellow_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_137])).
% 2.37/1.32  tff(c_369, plain, (~l1_struct_0(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_356, c_139])).
% 2.37/1.32  tff(c_373, plain, (~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_369])).
% 2.37/1.32  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_373])).
% 2.37/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  Inference rules
% 2.37/1.32  ----------------------
% 2.37/1.32  #Ref     : 0
% 2.37/1.32  #Sup     : 68
% 2.37/1.32  #Fact    : 0
% 2.37/1.32  #Define  : 0
% 2.37/1.32  #Split   : 2
% 2.37/1.32  #Chain   : 0
% 2.37/1.32  #Close   : 0
% 2.37/1.32  
% 2.37/1.32  Ordering : KBO
% 2.37/1.32  
% 2.37/1.32  Simplification rules
% 2.37/1.32  ----------------------
% 2.37/1.32  #Subsume      : 8
% 2.37/1.32  #Demod        : 20
% 2.37/1.32  #Tautology    : 33
% 2.37/1.32  #SimpNegUnit  : 5
% 2.37/1.32  #BackRed      : 5
% 2.37/1.32  
% 2.37/1.32  #Partial instantiations: 0
% 2.37/1.32  #Strategies tried      : 1
% 2.37/1.32  
% 2.37/1.32  Timing (in seconds)
% 2.37/1.32  ----------------------
% 2.37/1.32  Preprocessing        : 0.31
% 2.37/1.32  Parsing              : 0.16
% 2.37/1.32  CNF conversion       : 0.02
% 2.37/1.32  Main loop            : 0.23
% 2.37/1.32  Inferencing          : 0.08
% 2.37/1.32  Reduction            : 0.07
% 2.37/1.32  Demodulation         : 0.05
% 2.37/1.32  BG Simplification    : 0.01
% 2.37/1.32  Subsumption          : 0.04
% 2.37/1.32  Abstraction          : 0.01
% 2.37/1.32  MUC search           : 0.00
% 2.37/1.32  Cooper               : 0.00
% 2.37/1.32  Total                : 0.57
% 2.37/1.32  Index Insertion      : 0.00
% 2.37/1.32  Index Deletion       : 0.00
% 2.37/1.32  Index Matching       : 0.00
% 2.37/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
