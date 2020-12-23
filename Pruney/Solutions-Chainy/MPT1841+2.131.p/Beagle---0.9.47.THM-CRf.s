%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:45 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 143 expanded)
%              Number of leaves         :   45 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  116 ( 247 expanded)
%              Number of equality atoms :   28 (  44 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_92,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_109,axiom,(
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

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_46,plain,(
    ! [A_30] : l1_orders_2(k2_yellow_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,(
    ! [A_46,B_47] : k2_xboole_0(k1_tarski(A_46),B_47) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_99,plain,(
    ! [A_46] : k1_tarski(A_46) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_269,plain,(
    ! [A_85,B_86] :
      ( k6_domain_1(A_85,B_86) = k1_tarski(B_86)
      | ~ m1_subset_1(B_86,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_275,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_269])).

tff(c_279,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_275])).

tff(c_416,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1(k6_domain_1(A_105,B_106),k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_106,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_425,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_416])).

tff(c_429,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_425])).

tff(c_430,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_429])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_438,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_430,c_30])).

tff(c_450,plain,(
    ! [B_107,A_108] :
      ( B_107 = A_108
      | ~ r1_tarski(A_108,B_107)
      | ~ v1_zfmisc_1(B_107)
      | v1_xboole_0(B_107)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_453,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_438,c_450])).

tff(c_465,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_453])).

tff(c_466,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_465])).

tff(c_472,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_195,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_2'(A_68,B_69),A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,(
    ! [A_68,B_69] :
      ( ~ v1_xboole_0(A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_207,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_220,plain,(
    ! [A_74] :
      ( k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_207])).

tff(c_233,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_205,c_220])).

tff(c_477,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_472,c_233])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_477])).

tff(c_483,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_56,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_280,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_56])).

tff(c_487,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_280])).

tff(c_48,plain,(
    ! [A_31] : u1_struct_0(k2_yellow_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_115,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_120,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_orders_2(A_52) ) ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_123,plain,(
    ! [A_30] : u1_struct_0(k2_yellow_1(A_30)) = k2_struct_0(k2_yellow_1(A_30)) ),
    inference(resolution,[status(thm)],[c_46,c_120])).

tff(c_125,plain,(
    ! [A_30] : k2_struct_0(k2_yellow_1(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_123])).

tff(c_136,plain,(
    ! [A_56] :
      ( ~ v1_subset_1(k2_struct_0(A_56),u1_struct_0(A_56))
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,(
    ! [A_31] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_31)),A_31)
      | ~ l1_struct_0(k2_yellow_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_136])).

tff(c_144,plain,(
    ! [A_31] :
      ( ~ v1_subset_1(A_31,A_31)
      | ~ l1_struct_0(k2_yellow_1(A_31)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_142])).

tff(c_506,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_487,c_144])).

tff(c_510,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_506])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:24:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.44  
% 2.58/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.45  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.58/1.45  
% 2.58/1.45  %Foreground sorts:
% 2.58/1.45  
% 2.58/1.45  
% 2.58/1.45  %Background operators:
% 2.58/1.45  
% 2.58/1.45  
% 2.58/1.45  %Foreground operators:
% 2.58/1.45  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.58/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.45  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.58/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.58/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.45  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.58/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.58/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.58/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.58/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.45  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.58/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.58/1.45  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.58/1.45  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.58/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.58/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.58/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.45  
% 2.58/1.46  tff(f_92, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.58/1.46  tff(f_81, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.58/1.46  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.58/1.46  tff(f_57, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.58/1.46  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.58/1.46  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.58/1.46  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.58/1.46  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.58/1.46  tff(f_109, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.58/1.46  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.58/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.58/1.46  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.58/1.46  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.46  tff(f_96, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.58/1.46  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.58/1.46  tff(f_70, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.58/1.46  tff(c_46, plain, (![A_30]: (l1_orders_2(k2_yellow_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.58/1.46  tff(c_40, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.58/1.46  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.58/1.46  tff(c_95, plain, (![A_46, B_47]: (k2_xboole_0(k1_tarski(A_46), B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.58/1.46  tff(c_99, plain, (![A_46]: (k1_tarski(A_46)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_95])).
% 2.58/1.46  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.58/1.46  tff(c_54, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.58/1.46  tff(c_58, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.58/1.46  tff(c_269, plain, (![A_85, B_86]: (k6_domain_1(A_85, B_86)=k1_tarski(B_86) | ~m1_subset_1(B_86, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.58/1.46  tff(c_275, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_269])).
% 2.58/1.46  tff(c_279, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_275])).
% 2.58/1.46  tff(c_416, plain, (![A_105, B_106]: (m1_subset_1(k6_domain_1(A_105, B_106), k1_zfmisc_1(A_105)) | ~m1_subset_1(B_106, A_105) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.58/1.46  tff(c_425, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_279, c_416])).
% 2.58/1.46  tff(c_429, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_425])).
% 2.58/1.46  tff(c_430, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_429])).
% 2.58/1.46  tff(c_30, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.46  tff(c_438, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_430, c_30])).
% 2.58/1.46  tff(c_450, plain, (![B_107, A_108]: (B_107=A_108 | ~r1_tarski(A_108, B_107) | ~v1_zfmisc_1(B_107) | v1_xboole_0(B_107) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.58/1.46  tff(c_453, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_438, c_450])).
% 2.58/1.46  tff(c_465, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_453])).
% 2.58/1.46  tff(c_466, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_465])).
% 2.58/1.46  tff(c_472, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_466])).
% 2.58/1.46  tff(c_195, plain, (![A_68, B_69]: (r2_hidden('#skF_2'(A_68, B_69), A_68) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.46  tff(c_205, plain, (![A_68, B_69]: (~v1_xboole_0(A_68) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_195, c_2])).
% 2.58/1.46  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.58/1.46  tff(c_207, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.58/1.46  tff(c_220, plain, (![A_74]: (k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_207])).
% 2.58/1.46  tff(c_233, plain, (![A_68]: (k1_xboole_0=A_68 | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_205, c_220])).
% 2.58/1.46  tff(c_477, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_472, c_233])).
% 2.58/1.46  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_477])).
% 2.58/1.46  tff(c_483, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_466])).
% 2.58/1.46  tff(c_56, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.58/1.46  tff(c_280, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_56])).
% 2.58/1.46  tff(c_487, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_280])).
% 2.58/1.46  tff(c_48, plain, (![A_31]: (u1_struct_0(k2_yellow_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.58/1.46  tff(c_115, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.58/1.46  tff(c_120, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_orders_2(A_52))), inference(resolution, [status(thm)], [c_40, c_115])).
% 2.58/1.46  tff(c_123, plain, (![A_30]: (u1_struct_0(k2_yellow_1(A_30))=k2_struct_0(k2_yellow_1(A_30)))), inference(resolution, [status(thm)], [c_46, c_120])).
% 2.58/1.46  tff(c_125, plain, (![A_30]: (k2_struct_0(k2_yellow_1(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_123])).
% 2.58/1.46  tff(c_136, plain, (![A_56]: (~v1_subset_1(k2_struct_0(A_56), u1_struct_0(A_56)) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.58/1.46  tff(c_142, plain, (![A_31]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_31)), A_31) | ~l1_struct_0(k2_yellow_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_136])).
% 2.58/1.46  tff(c_144, plain, (![A_31]: (~v1_subset_1(A_31, A_31) | ~l1_struct_0(k2_yellow_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_142])).
% 2.58/1.46  tff(c_506, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_487, c_144])).
% 2.58/1.46  tff(c_510, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_506])).
% 2.58/1.46  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_510])).
% 2.58/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.46  
% 2.58/1.46  Inference rules
% 2.58/1.46  ----------------------
% 2.58/1.46  #Ref     : 0
% 2.58/1.46  #Sup     : 94
% 2.58/1.46  #Fact    : 0
% 2.58/1.46  #Define  : 0
% 2.58/1.46  #Split   : 2
% 2.58/1.46  #Chain   : 0
% 2.58/1.46  #Close   : 0
% 2.58/1.46  
% 2.58/1.46  Ordering : KBO
% 2.58/1.46  
% 2.58/1.46  Simplification rules
% 2.58/1.46  ----------------------
% 2.58/1.46  #Subsume      : 15
% 2.58/1.46  #Demod        : 29
% 2.58/1.46  #Tautology    : 44
% 2.58/1.46  #SimpNegUnit  : 11
% 2.58/1.46  #BackRed      : 15
% 2.58/1.46  
% 2.58/1.46  #Partial instantiations: 0
% 2.58/1.46  #Strategies tried      : 1
% 2.58/1.46  
% 2.58/1.46  Timing (in seconds)
% 2.58/1.46  ----------------------
% 2.58/1.46  Preprocessing        : 0.36
% 2.58/1.46  Parsing              : 0.19
% 2.58/1.46  CNF conversion       : 0.03
% 2.58/1.46  Main loop            : 0.27
% 2.58/1.46  Inferencing          : 0.10
% 2.58/1.47  Reduction            : 0.08
% 2.58/1.47  Demodulation         : 0.06
% 2.58/1.47  BG Simplification    : 0.02
% 2.58/1.47  Subsumption          : 0.05
% 2.58/1.47  Abstraction          : 0.02
% 2.58/1.47  MUC search           : 0.00
% 2.58/1.47  Cooper               : 0.00
% 2.58/1.47  Total                : 0.66
% 2.58/1.47  Index Insertion      : 0.00
% 2.58/1.47  Index Deletion       : 0.00
% 2.58/1.47  Index Matching       : 0.00
% 2.58/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
