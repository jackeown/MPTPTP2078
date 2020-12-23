%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:02 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 314 expanded)
%              Number of leaves         :   44 ( 141 expanded)
%              Depth                    :   20
%              Number of atoms          :  185 (1037 expanded)
%              Number of equality atoms :   15 ( 113 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
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

tff(f_140,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,axiom,(
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

tff(f_124,axiom,(
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

tff(f_82,axiom,(
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

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_56,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_54,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_216,plain,(
    ! [A_86,B_87] :
      ( ~ v1_xboole_0(k4_orders_2(A_86,B_87))
      | ~ m1_orders_1(B_87,k1_orders_1(u1_struct_0(A_86)))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_219,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_216])).

tff(c_222,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_219])).

tff(c_223,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_222])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_10] : k3_tarski(k1_tarski(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_104,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k3_tarski(A_76),k3_tarski(B_77))
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_152,plain,(
    ! [A_81] :
      ( r1_tarski(k3_tarski(A_81),k1_xboole_0)
      | ~ r1_tarski(A_81,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_104])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [B_78,A_79] :
      ( B_78 = A_79
      | ~ r1_tarski(B_78,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_118])).

tff(c_260,plain,(
    ! [A_89] :
      ( k3_tarski(A_89) = k1_xboole_0
      | ~ r1_tarski(A_89,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_152,c_133])).

tff(c_268,plain,(
    ! [A_8] :
      ( k3_tarski(k1_tarski(A_8)) = k1_xboole_0
      | ~ r2_hidden(A_8,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_16,c_260])).

tff(c_293,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ r2_hidden(A_90,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_268])).

tff(c_297,plain,
    ( '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_293])).

tff(c_300,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_297])).

tff(c_304,plain,
    ( v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_4])).

tff(c_307,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_304])).

tff(c_627,plain,(
    ! [D_116,A_117,B_118] :
      ( m2_orders_2(D_116,A_117,B_118)
      | ~ r2_hidden(D_116,k4_orders_2(A_117,B_118))
      | ~ m1_orders_1(B_118,k1_orders_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_629,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_307,c_627])).

tff(c_635,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_629])).

tff(c_636,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_635])).

tff(c_48,plain,(
    ! [C_60,A_57,B_58] :
      ( v6_orders_2(C_60,A_57)
      | ~ m2_orders_2(C_60,A_57,B_58)
      | ~ m1_orders_1(B_58,k1_orders_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_641,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_636,c_48])).

tff(c_648,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_641])).

tff(c_649,plain,(
    v6_orders_2(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_648])).

tff(c_46,plain,(
    ! [C_60,A_57,B_58] :
      ( m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m2_orders_2(C_60,A_57,B_58)
      | ~ m1_orders_1(B_58,k1_orders_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_639,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_636,c_46])).

tff(c_644,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_639])).

tff(c_645,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_644])).

tff(c_883,plain,(
    ! [A_138,B_139] :
      ( ~ m2_orders_2(k1_xboole_0,A_138,B_139)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ v6_orders_2(k1_xboole_0,A_138)
      | ~ m1_orders_1(B_139,k1_orders_1(u1_struct_0(A_138)))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_885,plain,(
    ! [B_139] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_139)
      | ~ v6_orders_2(k1_xboole_0,'#skF_5')
      | ~ m1_orders_1(B_139,k1_orders_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_645,c_883])).

tff(c_888,plain,(
    ! [B_139] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_139)
      | ~ m1_orders_1(B_139,k1_orders_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_649,c_885])).

tff(c_941,plain,(
    ! [B_142] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_142)
      | ~ m1_orders_1(B_142,k1_orders_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_888])).

tff(c_944,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_941])).

tff(c_948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.46  
% 3.13/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.46  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.13/1.46  
% 3.13/1.46  %Foreground sorts:
% 3.13/1.46  
% 3.13/1.46  
% 3.13/1.46  %Background operators:
% 3.13/1.46  
% 3.13/1.46  
% 3.13/1.46  %Foreground operators:
% 3.13/1.46  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 3.13/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.13/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.13/1.46  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.13/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.46  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.13/1.46  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.13/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.13/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.46  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.13/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.13/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.13/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.13/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.46  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 3.13/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.13/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.13/1.46  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.13/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.46  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.13/1.46  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.13/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.46  
% 3.25/1.48  tff(f_158, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 3.25/1.48  tff(f_140, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 3.25/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.25/1.48  tff(f_45, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.25/1.48  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.25/1.48  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 3.25/1.48  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.25/1.48  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.25/1.48  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 3.25/1.48  tff(f_124, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.25/1.48  tff(f_82, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 3.25/1.48  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.25/1.48  tff(c_62, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.25/1.48  tff(c_60, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.25/1.48  tff(c_58, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.25/1.48  tff(c_56, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.25/1.48  tff(c_54, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.25/1.48  tff(c_216, plain, (![A_86, B_87]: (~v1_xboole_0(k4_orders_2(A_86, B_87)) | ~m1_orders_1(B_87, k1_orders_1(u1_struct_0(A_86))) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.25/1.48  tff(c_219, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_216])).
% 3.25/1.48  tff(c_222, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_219])).
% 3.25/1.48  tff(c_223, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_222])).
% 3.25/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.48  tff(c_18, plain, (![A_10]: (k3_tarski(k1_tarski(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.25/1.48  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.48  tff(c_52, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.25/1.48  tff(c_104, plain, (![A_76, B_77]: (r1_tarski(k3_tarski(A_76), k3_tarski(B_77)) | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.25/1.48  tff(c_152, plain, (![A_81]: (r1_tarski(k3_tarski(A_81), k1_xboole_0) | ~r1_tarski(A_81, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_104])).
% 3.25/1.48  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.48  tff(c_118, plain, (![B_78, A_79]: (B_78=A_79 | ~r1_tarski(B_78, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.48  tff(c_133, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_118])).
% 3.25/1.48  tff(c_260, plain, (![A_89]: (k3_tarski(A_89)=k1_xboole_0 | ~r1_tarski(A_89, k4_orders_2('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_152, c_133])).
% 3.25/1.48  tff(c_268, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=k1_xboole_0 | ~r2_hidden(A_8, k4_orders_2('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_16, c_260])).
% 3.25/1.48  tff(c_293, plain, (![A_90]: (k1_xboole_0=A_90 | ~r2_hidden(A_90, k4_orders_2('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_268])).
% 3.25/1.48  tff(c_297, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_293])).
% 3.25/1.48  tff(c_300, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_223, c_297])).
% 3.25/1.48  tff(c_304, plain, (v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_4])).
% 3.25/1.48  tff(c_307, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_223, c_304])).
% 3.25/1.48  tff(c_627, plain, (![D_116, A_117, B_118]: (m2_orders_2(D_116, A_117, B_118) | ~r2_hidden(D_116, k4_orders_2(A_117, B_118)) | ~m1_orders_1(B_118, k1_orders_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.25/1.48  tff(c_629, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_307, c_627])).
% 3.25/1.48  tff(c_635, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_629])).
% 3.25/1.48  tff(c_636, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_635])).
% 3.25/1.48  tff(c_48, plain, (![C_60, A_57, B_58]: (v6_orders_2(C_60, A_57) | ~m2_orders_2(C_60, A_57, B_58) | ~m1_orders_1(B_58, k1_orders_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.25/1.48  tff(c_641, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_636, c_48])).
% 3.25/1.48  tff(c_648, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_641])).
% 3.25/1.48  tff(c_649, plain, (v6_orders_2(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_648])).
% 3.25/1.48  tff(c_46, plain, (![C_60, A_57, B_58]: (m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_57))) | ~m2_orders_2(C_60, A_57, B_58) | ~m1_orders_1(B_58, k1_orders_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.25/1.48  tff(c_639, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_636, c_46])).
% 3.25/1.48  tff(c_644, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_639])).
% 3.25/1.48  tff(c_645, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_644])).
% 3.25/1.48  tff(c_883, plain, (![A_138, B_139]: (~m2_orders_2(k1_xboole_0, A_138, B_139) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_138))) | ~v6_orders_2(k1_xboole_0, A_138) | ~m1_orders_1(B_139, k1_orders_1(u1_struct_0(A_138))) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.25/1.48  tff(c_885, plain, (![B_139]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_139) | ~v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1(B_139, k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_645, c_883])).
% 3.25/1.48  tff(c_888, plain, (![B_139]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_139) | ~m1_orders_1(B_139, k1_orders_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_649, c_885])).
% 3.25/1.48  tff(c_941, plain, (![B_142]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_142) | ~m1_orders_1(B_142, k1_orders_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_888])).
% 3.25/1.48  tff(c_944, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_941])).
% 3.25/1.48  tff(c_948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_636, c_944])).
% 3.25/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.48  
% 3.25/1.48  Inference rules
% 3.25/1.48  ----------------------
% 3.25/1.48  #Ref     : 0
% 3.25/1.48  #Sup     : 184
% 3.25/1.48  #Fact    : 0
% 3.25/1.48  #Define  : 0
% 3.25/1.48  #Split   : 1
% 3.25/1.48  #Chain   : 0
% 3.25/1.48  #Close   : 0
% 3.25/1.48  
% 3.25/1.48  Ordering : KBO
% 3.25/1.48  
% 3.25/1.48  Simplification rules
% 3.25/1.48  ----------------------
% 3.25/1.48  #Subsume      : 7
% 3.25/1.48  #Demod        : 137
% 3.25/1.48  #Tautology    : 95
% 3.25/1.48  #SimpNegUnit  : 16
% 3.25/1.48  #BackRed      : 0
% 3.25/1.48  
% 3.25/1.48  #Partial instantiations: 0
% 3.25/1.48  #Strategies tried      : 1
% 3.25/1.48  
% 3.25/1.48  Timing (in seconds)
% 3.25/1.48  ----------------------
% 3.25/1.48  Preprocessing        : 0.34
% 3.25/1.48  Parsing              : 0.18
% 3.25/1.48  CNF conversion       : 0.03
% 3.25/1.48  Main loop            : 0.37
% 3.25/1.48  Inferencing          : 0.13
% 3.25/1.48  Reduction            : 0.12
% 3.25/1.48  Demodulation         : 0.08
% 3.25/1.48  BG Simplification    : 0.02
% 3.25/1.48  Subsumption          : 0.08
% 3.25/1.48  Abstraction          : 0.02
% 3.25/1.48  MUC search           : 0.00
% 3.25/1.48  Cooper               : 0.00
% 3.25/1.48  Total                : 0.75
% 3.25/1.48  Index Insertion      : 0.00
% 3.25/1.48  Index Deletion       : 0.00
% 3.25/1.48  Index Matching       : 0.00
% 3.25/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
