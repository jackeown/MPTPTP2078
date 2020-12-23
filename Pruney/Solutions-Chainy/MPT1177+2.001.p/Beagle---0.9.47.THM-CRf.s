%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:55 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 416 expanded)
%              Number of leaves         :   38 ( 168 expanded)
%              Depth                    :   15
%              Number of atoms          :  310 (1831 expanded)
%              Number of equality atoms :   25 (  88 expanded)
%              Maximal formula depth    :   16 (   4 average)
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_189,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_91,axiom,(
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

tff(f_110,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_136,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

tff(f_71,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_164,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_42,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_44,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_52,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_50,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_48,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_46,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_180,plain,(
    ! [C_99,A_100,B_101] :
      ( v6_orders_2(C_99,A_100)
      | ~ m2_orders_2(C_99,A_100,B_101)
      | ~ m1_orders_1(B_101,k1_orders_1(u1_struct_0(A_100)))
      | ~ l1_orders_2(A_100)
      | ~ v5_orders_2(A_100)
      | ~ v4_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_182,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_180])).

tff(c_185,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_182])).

tff(c_186,plain,(
    v6_orders_2('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_185])).

tff(c_76,plain,(
    ! [A_73,B_74] :
      ( r2_xboole_0(A_73,B_74)
      | B_74 = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_67,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_87,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_67])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_68,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_62])).

tff(c_96,plain,(
    ! [C_78,B_79,A_80] :
      ( r1_tarski(C_78,B_79)
      | ~ m1_orders_2(C_78,A_80,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_98,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_101,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_98])).

tff(c_102,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_93,c_101])).

tff(c_40,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_116,plain,(
    ! [C_84,A_85,B_86] :
      ( m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m2_orders_2(C_84,A_85,B_86)
      | ~ m1_orders_1(B_86,k1_orders_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_120,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_116])).

tff(c_127,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_120])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_102,c_127])).

tff(c_130,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_132,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_68])).

tff(c_142,plain,(
    ! [B_88,A_89] :
      ( ~ m1_orders_2(B_88,A_89,B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_144,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_142])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144])).

tff(c_148,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_147])).

tff(c_149,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_164,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m2_orders_2(C_96,A_97,B_98)
      | ~ m1_orders_1(B_98,k1_orders_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_166,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_164])).

tff(c_169,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_149,c_169])).

tff(c_173,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_24,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_218,plain,(
    ! [A_111,B_112] :
      ( ~ m2_orders_2('#skF_4',A_111,B_112)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ v6_orders_2('#skF_4',A_111)
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0(A_111)))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_172,c_172,c_24])).

tff(c_220,plain,(
    ! [B_112] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_112)
      | ~ v6_orders_2('#skF_4','#skF_2')
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_173,c_218])).

tff(c_223,plain,(
    ! [B_112] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_112)
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_186,c_220])).

tff(c_225,plain,(
    ! [B_113] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_113)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_223])).

tff(c_228,plain,(
    ~ m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_228])).

tff(c_234,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_238,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_234,c_6])).

tff(c_253,plain,(
    ! [B_116,A_117] :
      ( B_116 = A_117
      | ~ r1_tarski(B_116,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_258,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_253])).

tff(c_263,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_280,plain,(
    ! [C_127,A_128,B_129] :
      ( m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m2_orders_2(C_127,A_128,B_129)
      | ~ m1_orders_1(B_129,k1_orders_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_282,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_280])).

tff(c_287,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_282])).

tff(c_288,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_287])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_233,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_307,plain,(
    ! [C_135,A_136,D_137,B_138] :
      ( m1_orders_2(C_135,A_136,D_137)
      | m1_orders_2(D_137,A_136,C_135)
      | D_137 = C_135
      | ~ m2_orders_2(D_137,A_136,B_138)
      | ~ m2_orders_2(C_135,A_136,B_138)
      | ~ m1_orders_1(B_138,k1_orders_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_309,plain,(
    ! [C_135] :
      ( m1_orders_2(C_135,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_135)
      | C_135 = '#skF_4'
      | ~ m2_orders_2(C_135,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_307])).

tff(c_314,plain,(
    ! [C_135] :
      ( m1_orders_2(C_135,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_135)
      | C_135 = '#skF_4'
      | ~ m2_orders_2(C_135,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_309])).

tff(c_320,plain,(
    ! [C_139] :
      ( m1_orders_2(C_139,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_139)
      | C_139 = '#skF_4'
      | ~ m2_orders_2(C_139,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_314])).

tff(c_326,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_320])).

tff(c_331,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_326])).

tff(c_332,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_336,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_263])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_336])).

tff(c_347,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_30,plain,(
    ! [C_37,B_35,A_31] :
      ( r1_tarski(C_37,B_35)
      | ~ m1_orders_2(C_37,A_31,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_350,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_347,c_30])).

tff(c_353,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_288,c_350])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_263,c_353])).

tff(c_356,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_360,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_234])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.33  
% 2.59/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.33  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.59/1.33  
% 2.59/1.33  %Foreground sorts:
% 2.59/1.33  
% 2.59/1.33  
% 2.59/1.33  %Background operators:
% 2.59/1.33  
% 2.59/1.33  
% 2.59/1.33  %Foreground operators:
% 2.59/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.33  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.59/1.33  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.59/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.33  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.59/1.33  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.59/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.33  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.59/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.33  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.59/1.33  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.59/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.33  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.59/1.33  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.59/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.59/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.59/1.33  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.59/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.33  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.59/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.33  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.59/1.33  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.59/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.33  
% 2.59/1.36  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.59/1.36  tff(f_189, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.59/1.36  tff(f_91, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.59/1.36  tff(f_110, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.59/1.36  tff(f_136, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_orders_2)).
% 2.59/1.36  tff(f_71, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 2.59/1.36  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.59/1.36  tff(f_164, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.59/1.36  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.36  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_42, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_44, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_52, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_50, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_48, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_46, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_180, plain, (![C_99, A_100, B_101]: (v6_orders_2(C_99, A_100) | ~m2_orders_2(C_99, A_100, B_101) | ~m1_orders_1(B_101, k1_orders_1(u1_struct_0(A_100))) | ~l1_orders_2(A_100) | ~v5_orders_2(A_100) | ~v4_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.59/1.36  tff(c_182, plain, (v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_180])).
% 2.59/1.36  tff(c_185, plain, (v6_orders_2('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_182])).
% 2.59/1.36  tff(c_186, plain, (v6_orders_2('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_185])).
% 2.59/1.36  tff(c_76, plain, (![A_73, B_74]: (r2_xboole_0(A_73, B_74) | B_74=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.36  tff(c_56, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_67, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 2.59/1.36  tff(c_87, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_67])).
% 2.59/1.36  tff(c_93, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_87])).
% 2.59/1.36  tff(c_62, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_68, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_67, c_62])).
% 2.59/1.36  tff(c_96, plain, (![C_78, B_79, A_80]: (r1_tarski(C_78, B_79) | ~m1_orders_2(C_78, A_80, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.59/1.36  tff(c_98, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_96])).
% 2.59/1.36  tff(c_101, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_98])).
% 2.59/1.36  tff(c_102, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_93, c_101])).
% 2.59/1.36  tff(c_40, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.59/1.36  tff(c_116, plain, (![C_84, A_85, B_86]: (m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~m2_orders_2(C_84, A_85, B_86) | ~m1_orders_1(B_86, k1_orders_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.59/1.36  tff(c_120, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_116])).
% 2.59/1.36  tff(c_127, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_120])).
% 2.59/1.36  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_102, c_127])).
% 2.59/1.36  tff(c_130, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_87])).
% 2.59/1.36  tff(c_132, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_68])).
% 2.59/1.36  tff(c_142, plain, (![B_88, A_89]: (~m1_orders_2(B_88, A_89, B_88) | k1_xboole_0=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.59/1.36  tff(c_144, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_132, c_142])).
% 2.59/1.36  tff(c_147, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144])).
% 2.59/1.36  tff(c_148, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_147])).
% 2.59/1.36  tff(c_149, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_148])).
% 2.59/1.36  tff(c_164, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m2_orders_2(C_96, A_97, B_98) | ~m1_orders_1(B_98, k1_orders_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.59/1.36  tff(c_166, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_164])).
% 2.59/1.36  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_166])).
% 2.59/1.36  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_149, c_169])).
% 2.59/1.36  tff(c_173, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_148])).
% 2.59/1.36  tff(c_172, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_148])).
% 2.59/1.36  tff(c_24, plain, (![A_5, B_17]: (~m2_orders_2(k1_xboole_0, A_5, B_17) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_5))) | ~v6_orders_2(k1_xboole_0, A_5) | ~m1_orders_1(B_17, k1_orders_1(u1_struct_0(A_5))) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5) | ~v4_orders_2(A_5) | ~v3_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.59/1.36  tff(c_218, plain, (![A_111, B_112]: (~m2_orders_2('#skF_4', A_111, B_112) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_111))) | ~v6_orders_2('#skF_4', A_111) | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0(A_111))) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_172, c_172, c_24])).
% 2.59/1.36  tff(c_220, plain, (![B_112]: (~m2_orders_2('#skF_4', '#skF_2', B_112) | ~v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_173, c_218])).
% 2.59/1.36  tff(c_223, plain, (![B_112]: (~m2_orders_2('#skF_4', '#skF_2', B_112) | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_186, c_220])).
% 2.59/1.36  tff(c_225, plain, (![B_113]: (~m2_orders_2('#skF_4', '#skF_2', B_113) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_223])).
% 2.59/1.36  tff(c_228, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_225])).
% 2.59/1.36  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_228])).
% 2.59/1.36  tff(c_234, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 2.59/1.36  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.36  tff(c_238, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_234, c_6])).
% 2.59/1.36  tff(c_253, plain, (![B_116, A_117]: (B_116=A_117 | ~r1_tarski(B_116, A_117) | ~r1_tarski(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.36  tff(c_258, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_238, c_253])).
% 2.59/1.36  tff(c_263, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_258])).
% 2.59/1.36  tff(c_280, plain, (![C_127, A_128, B_129]: (m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~m2_orders_2(C_127, A_128, B_129) | ~m1_orders_1(B_129, k1_orders_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.59/1.36  tff(c_282, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_280])).
% 2.59/1.36  tff(c_287, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_282])).
% 2.59/1.36  tff(c_288, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_287])).
% 2.59/1.36  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.36  tff(c_233, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 2.59/1.36  tff(c_307, plain, (![C_135, A_136, D_137, B_138]: (m1_orders_2(C_135, A_136, D_137) | m1_orders_2(D_137, A_136, C_135) | D_137=C_135 | ~m2_orders_2(D_137, A_136, B_138) | ~m2_orders_2(C_135, A_136, B_138) | ~m1_orders_1(B_138, k1_orders_1(u1_struct_0(A_136))) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.59/1.36  tff(c_309, plain, (![C_135]: (m1_orders_2(C_135, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_135) | C_135='#skF_4' | ~m2_orders_2(C_135, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_307])).
% 2.59/1.36  tff(c_314, plain, (![C_135]: (m1_orders_2(C_135, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_135) | C_135='#skF_4' | ~m2_orders_2(C_135, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_309])).
% 2.59/1.36  tff(c_320, plain, (![C_139]: (m1_orders_2(C_139, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_139) | C_139='#skF_4' | ~m2_orders_2(C_139, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_314])).
% 2.59/1.36  tff(c_326, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_320])).
% 2.59/1.36  tff(c_331, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_233, c_326])).
% 2.59/1.36  tff(c_332, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_331])).
% 2.59/1.36  tff(c_336, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_263])).
% 2.59/1.36  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_336])).
% 2.59/1.36  tff(c_347, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_331])).
% 2.59/1.36  tff(c_30, plain, (![C_37, B_35, A_31]: (r1_tarski(C_37, B_35) | ~m1_orders_2(C_37, A_31, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_orders_2(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.59/1.36  tff(c_350, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_347, c_30])).
% 2.59/1.36  tff(c_353, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_288, c_350])).
% 2.59/1.36  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_263, c_353])).
% 2.59/1.36  tff(c_356, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_258])).
% 2.59/1.36  tff(c_360, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_234])).
% 2.59/1.36  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_360])).
% 2.59/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.36  
% 2.59/1.36  Inference rules
% 2.59/1.36  ----------------------
% 2.59/1.36  #Ref     : 0
% 2.59/1.36  #Sup     : 40
% 2.59/1.36  #Fact    : 0
% 2.59/1.36  #Define  : 0
% 2.59/1.36  #Split   : 5
% 2.59/1.36  #Chain   : 0
% 2.59/1.36  #Close   : 0
% 2.59/1.36  
% 2.59/1.36  Ordering : KBO
% 2.59/1.36  
% 2.59/1.36  Simplification rules
% 2.59/1.36  ----------------------
% 2.59/1.36  #Subsume      : 2
% 2.59/1.36  #Demod        : 161
% 2.59/1.36  #Tautology    : 25
% 2.59/1.36  #SimpNegUnit  : 27
% 2.59/1.36  #BackRed      : 17
% 2.59/1.36  
% 2.59/1.36  #Partial instantiations: 0
% 2.59/1.36  #Strategies tried      : 1
% 2.59/1.36  
% 2.59/1.36  Timing (in seconds)
% 2.59/1.36  ----------------------
% 2.59/1.36  Preprocessing        : 0.34
% 2.59/1.36  Parsing              : 0.18
% 2.59/1.36  CNF conversion       : 0.03
% 2.59/1.36  Main loop            : 0.26
% 2.59/1.36  Inferencing          : 0.09
% 2.59/1.36  Reduction            : 0.09
% 2.59/1.36  Demodulation         : 0.06
% 2.59/1.36  BG Simplification    : 0.02
% 2.59/1.36  Subsumption          : 0.05
% 2.59/1.36  Abstraction          : 0.01
% 2.59/1.36  MUC search           : 0.00
% 2.59/1.36  Cooper               : 0.00
% 2.59/1.36  Total                : 0.64
% 2.59/1.36  Index Insertion      : 0.00
% 2.59/1.36  Index Deletion       : 0.00
% 2.59/1.36  Index Matching       : 0.00
% 2.59/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
