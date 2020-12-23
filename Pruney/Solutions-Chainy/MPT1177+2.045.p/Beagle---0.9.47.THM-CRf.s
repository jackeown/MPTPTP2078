%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:01 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 431 expanded)
%              Number of leaves         :   38 ( 178 expanded)
%              Depth                    :   15
%              Number of atoms          :  299 (1975 expanded)
%              Number of equality atoms :   19 (  60 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_205,negated_conjecture,(
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

tff(f_108,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_127,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_152,axiom,(
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
             => ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,C)
                  & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_70,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_180,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_40,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_42,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_84,plain,(
    ! [C_82,A_83,B_84] :
      ( v6_orders_2(C_82,A_83)
      | ~ m2_orders_2(C_82,A_83,B_84)
      | ~ m1_orders_1(B_84,k1_orders_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_86,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_84])).

tff(c_91,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_86])).

tff(c_92,plain,(
    v6_orders_2('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_91])).

tff(c_147,plain,(
    ! [C_98,A_99,B_100] :
      ( m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m2_orders_2(C_98,A_99,B_100)
      | ~ m1_orders_1(B_100,k1_orders_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_149,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_147])).

tff(c_152,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_149])).

tff(c_153,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_152])).

tff(c_65,plain,(
    ! [A_80,B_81] :
      ( r2_xboole_0(A_80,B_81)
      | B_81 = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_60,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_64,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_79,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_65,c_64])).

tff(c_97,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_99,plain,(
    ! [C_87,B_88,A_89] :
      ( r1_tarski(C_87,B_88)
      | ~ m1_orders_2(C_87,A_89,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_101,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_99])).

tff(c_104,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_101])).

tff(c_105,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_97,c_104])).

tff(c_36,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_106,plain,(
    ! [C_90,A_91,B_92] :
      ( m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m2_orders_2(C_90,A_91,B_92)
      | ~ m1_orders_1(B_92,k1_orders_1(u1_struct_0(A_91)))
      | ~ l1_orders_2(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v4_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_110,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_117,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_110])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_105,c_117])).

tff(c_120,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_124,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60])).

tff(c_162,plain,(
    ! [C_106,A_107,B_108] :
      ( ~ m1_orders_2(C_106,A_107,B_108)
      | ~ m1_orders_2(B_108,A_107,C_106)
      | k1_xboole_0 = B_108
      | ~ m1_subset_1(C_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_164,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_162])).

tff(c_167,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_153,c_124,c_164])).

tff(c_168,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_167])).

tff(c_20,plain,(
    ! [A_5,B_17] :
      ( ~ m2_orders_2(k1_xboole_0,A_5,B_17)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ v6_orders_2(k1_xboole_0,A_5)
      | ~ m1_orders_1(B_17,k1_orders_1(u1_struct_0(A_5)))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5)
      | ~ v4_orders_2(A_5)
      | ~ v3_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_182,plain,(
    ! [A_112,B_113] :
      ( ~ m2_orders_2('#skF_4',A_112,B_113)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v6_orders_2('#skF_4',A_112)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_168,c_168,c_20])).

tff(c_184,plain,(
    ! [B_113] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_113)
      | ~ v6_orders_2('#skF_4','#skF_2')
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_153,c_182])).

tff(c_187,plain,(
    ! [B_113] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_113)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_92,c_184])).

tff(c_189,plain,(
    ! [B_114] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_114)
      | ~ m1_orders_1(B_114,k1_orders_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_187])).

tff(c_192,plain,(
    ~ m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_189])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_192])).

tff(c_197,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_210,plain,(
    ! [B_117,A_118] :
      ( ~ r2_xboole_0(B_117,A_118)
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_214,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_197,c_210])).

tff(c_249,plain,(
    ! [C_132,A_133,B_134] :
      ( m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m2_orders_2(C_132,A_133,B_134)
      | ~ m1_orders_1(B_134,k1_orders_1(u1_struct_0(A_133)))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_251,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_249])).

tff(c_256,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_251])).

tff(c_257,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_256])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_199,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_199])).

tff(c_202,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_278,plain,(
    ! [C_147,A_148,D_149,B_150] :
      ( m1_orders_2(C_147,A_148,D_149)
      | m1_orders_2(D_149,A_148,C_147)
      | D_149 = C_147
      | ~ m2_orders_2(D_149,A_148,B_150)
      | ~ m2_orders_2(C_147,A_148,B_150)
      | ~ m1_orders_1(B_150,k1_orders_1(u1_struct_0(A_148)))
      | ~ l1_orders_2(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v4_orders_2(A_148)
      | ~ v3_orders_2(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_280,plain,(
    ! [C_147] :
      ( m1_orders_2(C_147,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_147)
      | C_147 = '#skF_4'
      | ~ m2_orders_2(C_147,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_278])).

tff(c_285,plain,(
    ! [C_147] :
      ( m1_orders_2(C_147,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_147)
      | C_147 = '#skF_4'
      | ~ m2_orders_2(C_147,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_280])).

tff(c_291,plain,(
    ! [C_151] :
      ( m1_orders_2(C_151,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_151)
      | C_151 = '#skF_4'
      | ~ m2_orders_2(C_151,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_285])).

tff(c_297,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_291])).

tff(c_302,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_297])).

tff(c_303,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_323,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_197])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_323])).

tff(c_330,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_28,plain,(
    ! [C_41,B_39,A_35] :
      ( r1_tarski(C_41,B_39)
      | ~ m1_orders_2(C_41,A_35,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_orders_2(A_35)
      | ~ v5_orders_2(A_35)
      | ~ v4_orders_2(A_35)
      | ~ v3_orders_2(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_339,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_330,c_28])).

tff(c_354,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_257,c_339])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_214,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.45  
% 2.67/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.45  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.67/1.45  
% 2.67/1.45  %Foreground sorts:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Background operators:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Foreground operators:
% 2.67/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.67/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.67/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.67/1.45  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.45  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.67/1.45  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.67/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.45  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.67/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.67/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.67/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.45  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.67/1.45  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.67/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.67/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.67/1.45  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.45  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.67/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.45  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.67/1.45  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.67/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.45  
% 3.10/1.47  tff(f_205, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 3.10/1.47  tff(f_108, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.10/1.47  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.10/1.47  tff(f_127, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.10/1.47  tff(f_152, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.10/1.47  tff(f_70, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 3.10/1.47  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.10/1.47  tff(f_180, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 3.10/1.47  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_40, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_42, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_84, plain, (![C_82, A_83, B_84]: (v6_orders_2(C_82, A_83) | ~m2_orders_2(C_82, A_83, B_84) | ~m1_orders_1(B_84, k1_orders_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.10/1.47  tff(c_86, plain, (v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_84])).
% 3.10/1.47  tff(c_91, plain, (v6_orders_2('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_86])).
% 3.10/1.47  tff(c_92, plain, (v6_orders_2('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_91])).
% 3.10/1.47  tff(c_147, plain, (![C_98, A_99, B_100]: (m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m2_orders_2(C_98, A_99, B_100) | ~m1_orders_1(B_100, k1_orders_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.10/1.47  tff(c_149, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_147])).
% 3.10/1.47  tff(c_152, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_149])).
% 3.10/1.47  tff(c_153, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_152])).
% 3.10/1.47  tff(c_65, plain, (![A_80, B_81]: (r2_xboole_0(A_80, B_81) | B_81=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.47  tff(c_58, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_60, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 3.10/1.47  tff(c_52, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_64, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 3.10/1.47  tff(c_79, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_65, c_64])).
% 3.10/1.47  tff(c_97, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_79])).
% 3.10/1.47  tff(c_99, plain, (![C_87, B_88, A_89]: (r1_tarski(C_87, B_88) | ~m1_orders_2(C_87, A_89, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.10/1.47  tff(c_101, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_99])).
% 3.10/1.47  tff(c_104, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_101])).
% 3.10/1.47  tff(c_105, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_97, c_104])).
% 3.10/1.47  tff(c_36, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.10/1.47  tff(c_106, plain, (![C_90, A_91, B_92]: (m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~m2_orders_2(C_90, A_91, B_92) | ~m1_orders_1(B_92, k1_orders_1(u1_struct_0(A_91))) | ~l1_orders_2(A_91) | ~v5_orders_2(A_91) | ~v4_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.10/1.47  tff(c_110, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_106])).
% 3.10/1.47  tff(c_117, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_110])).
% 3.10/1.47  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_105, c_117])).
% 3.10/1.47  tff(c_120, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_79])).
% 3.10/1.47  tff(c_124, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60])).
% 3.10/1.47  tff(c_162, plain, (![C_106, A_107, B_108]: (~m1_orders_2(C_106, A_107, B_108) | ~m1_orders_2(B_108, A_107, C_106) | k1_xboole_0=B_108 | ~m1_subset_1(C_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.10/1.47  tff(c_164, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_124, c_162])).
% 3.10/1.47  tff(c_167, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_153, c_124, c_164])).
% 3.10/1.47  tff(c_168, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_167])).
% 3.10/1.47  tff(c_20, plain, (![A_5, B_17]: (~m2_orders_2(k1_xboole_0, A_5, B_17) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_5))) | ~v6_orders_2(k1_xboole_0, A_5) | ~m1_orders_1(B_17, k1_orders_1(u1_struct_0(A_5))) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5) | ~v4_orders_2(A_5) | ~v3_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.47  tff(c_182, plain, (![A_112, B_113]: (~m2_orders_2('#skF_4', A_112, B_113) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_112))) | ~v6_orders_2('#skF_4', A_112) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_168, c_168, c_20])).
% 3.10/1.47  tff(c_184, plain, (![B_113]: (~m2_orders_2('#skF_4', '#skF_2', B_113) | ~v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_153, c_182])).
% 3.10/1.47  tff(c_187, plain, (![B_113]: (~m2_orders_2('#skF_4', '#skF_2', B_113) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_92, c_184])).
% 3.10/1.47  tff(c_189, plain, (![B_114]: (~m2_orders_2('#skF_4', '#skF_2', B_114) | ~m1_orders_1(B_114, k1_orders_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_187])).
% 3.10/1.47  tff(c_192, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_189])).
% 3.10/1.47  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_192])).
% 3.10/1.47  tff(c_197, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 3.10/1.47  tff(c_210, plain, (![B_117, A_118]: (~r2_xboole_0(B_117, A_118) | ~r1_tarski(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.47  tff(c_214, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_197, c_210])).
% 3.10/1.47  tff(c_249, plain, (![C_132, A_133, B_134]: (m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~m2_orders_2(C_132, A_133, B_134) | ~m1_orders_1(B_134, k1_orders_1(u1_struct_0(A_133))) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.10/1.47  tff(c_251, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_249])).
% 3.10/1.47  tff(c_256, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_251])).
% 3.10/1.47  tff(c_257, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_256])).
% 3.10/1.47  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.47  tff(c_199, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 3.10/1.47  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_199])).
% 3.10/1.47  tff(c_202, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 3.10/1.47  tff(c_278, plain, (![C_147, A_148, D_149, B_150]: (m1_orders_2(C_147, A_148, D_149) | m1_orders_2(D_149, A_148, C_147) | D_149=C_147 | ~m2_orders_2(D_149, A_148, B_150) | ~m2_orders_2(C_147, A_148, B_150) | ~m1_orders_1(B_150, k1_orders_1(u1_struct_0(A_148))) | ~l1_orders_2(A_148) | ~v5_orders_2(A_148) | ~v4_orders_2(A_148) | ~v3_orders_2(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.10/1.47  tff(c_280, plain, (![C_147]: (m1_orders_2(C_147, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_147) | C_147='#skF_4' | ~m2_orders_2(C_147, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_278])).
% 3.10/1.47  tff(c_285, plain, (![C_147]: (m1_orders_2(C_147, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_147) | C_147='#skF_4' | ~m2_orders_2(C_147, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_280])).
% 3.10/1.47  tff(c_291, plain, (![C_151]: (m1_orders_2(C_151, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_151) | C_151='#skF_4' | ~m2_orders_2(C_151, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_285])).
% 3.10/1.47  tff(c_297, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_291])).
% 3.10/1.47  tff(c_302, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_202, c_297])).
% 3.10/1.47  tff(c_303, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_302])).
% 3.10/1.47  tff(c_323, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_197])).
% 3.10/1.47  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_323])).
% 3.10/1.47  tff(c_330, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_302])).
% 3.10/1.47  tff(c_28, plain, (![C_41, B_39, A_35]: (r1_tarski(C_41, B_39) | ~m1_orders_2(C_41, A_35, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_orders_2(A_35) | ~v5_orders_2(A_35) | ~v4_orders_2(A_35) | ~v3_orders_2(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.10/1.47  tff(c_339, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_330, c_28])).
% 3.10/1.47  tff(c_354, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_257, c_339])).
% 3.10/1.47  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_214, c_354])).
% 3.10/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.47  
% 3.10/1.47  Inference rules
% 3.10/1.47  ----------------------
% 3.10/1.47  #Ref     : 0
% 3.10/1.47  #Sup     : 43
% 3.10/1.47  #Fact    : 0
% 3.10/1.47  #Define  : 0
% 3.10/1.47  #Split   : 4
% 3.10/1.47  #Chain   : 0
% 3.10/1.47  #Close   : 0
% 3.10/1.47  
% 3.10/1.47  Ordering : KBO
% 3.10/1.47  
% 3.10/1.47  Simplification rules
% 3.10/1.47  ----------------------
% 3.10/1.47  #Subsume      : 6
% 3.10/1.47  #Demod        : 153
% 3.10/1.47  #Tautology    : 22
% 3.10/1.47  #SimpNegUnit  : 26
% 3.10/1.47  #BackRed      : 15
% 3.10/1.47  
% 3.10/1.47  #Partial instantiations: 0
% 3.10/1.47  #Strategies tried      : 1
% 3.10/1.47  
% 3.10/1.47  Timing (in seconds)
% 3.10/1.47  ----------------------
% 3.10/1.48  Preprocessing        : 0.38
% 3.10/1.48  Parsing              : 0.22
% 3.10/1.48  CNF conversion       : 0.03
% 3.10/1.48  Main loop            : 0.26
% 3.10/1.48  Inferencing          : 0.09
% 3.10/1.48  Reduction            : 0.08
% 3.10/1.48  Demodulation         : 0.06
% 3.10/1.48  BG Simplification    : 0.02
% 3.10/1.48  Subsumption          : 0.04
% 3.10/1.48  Abstraction          : 0.01
% 3.10/1.48  MUC search           : 0.00
% 3.10/1.48  Cooper               : 0.00
% 3.10/1.48  Total                : 0.68
% 3.10/1.48  Index Insertion      : 0.00
% 3.10/1.48  Index Deletion       : 0.00
% 3.10/1.48  Index Matching       : 0.00
% 3.10/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
