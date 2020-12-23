%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:57 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 300 expanded)
%              Number of leaves         :   38 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  297 (1250 expanded)
%              Number of equality atoms :   21 (  45 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_211,negated_conjecture,(
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

tff(f_95,axiom,(
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

tff(f_114,axiom,(
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

tff(f_139,axiom,(
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

tff(f_158,axiom,(
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
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_186,axiom,(
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

tff(c_10,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_52,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_50,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_48,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_44,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_177,plain,(
    ! [C_109,A_110,B_111] :
      ( m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m2_orders_2(C_109,A_110,B_111)
      | ~ m1_orders_1(B_111,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_177])).

tff(c_182,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_179])).

tff(c_183,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_182])).

tff(c_70,plain,(
    ! [A_74,B_75] :
      ( r2_xboole_0(A_74,B_75)
      | B_75 = A_74
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_68,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_81,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_68])).

tff(c_87,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_69,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62])).

tff(c_118,plain,(
    ! [C_88,B_89,A_90] :
      ( r1_tarski(C_88,B_89)
      | ~ m1_orders_2(C_88,A_90,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_120,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_118])).

tff(c_123,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_120])).

tff(c_124,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_87,c_123])).

tff(c_125,plain,(
    ! [C_91,A_92,B_93] :
      ( m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m2_orders_2(C_91,A_92,B_93)
      | ~ m1_orders_1(B_93,k1_orders_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_127,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_125])).

tff(c_132,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_127])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_124,c_132])).

tff(c_135,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_137,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_69])).

tff(c_205,plain,(
    ! [C_119,A_120,B_121] :
      ( ~ m1_orders_2(C_119,A_120,B_121)
      | ~ m1_orders_2(B_121,A_120,C_119)
      | k1_xboole_0 = B_121
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_207,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_137,c_205])).

tff(c_210,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_183,c_137,c_207])).

tff(c_211,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_210])).

tff(c_199,plain,(
    ! [B_116,A_117,C_118] :
      ( r2_hidden(k1_funct_1(B_116,u1_struct_0(A_117)),C_118)
      | ~ m2_orders_2(C_118,A_117,B_116)
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_18,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_153,plain,(
    ! [C_96,B_97,A_98] :
      ( ~ v1_xboole_0(C_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(C_96))
      | ~ r2_hidden(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [A_7,A_98] :
      ( ~ v1_xboole_0(A_7)
      | ~ r2_hidden(A_98,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_161,plain,(
    ! [A_98] : ~ r2_hidden(A_98,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_204,plain,(
    ! [A_117,B_116] :
      ( ~ m2_orders_2(k1_xboole_0,A_117,B_116)
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_199,c_161])).

tff(c_235,plain,(
    ! [A_124,B_125] :
      ( ~ m2_orders_2('#skF_4',A_124,B_125)
      | ~ m1_orders_1(B_125,k1_orders_1(u1_struct_0(A_124)))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_204])).

tff(c_238,plain,
    ( ~ m2_orders_2('#skF_4','#skF_1','#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_235])).

tff(c_241,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_40,c_238])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_241])).

tff(c_244,plain,(
    ! [A_7] : ~ v1_xboole_0(A_7) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_8])).

tff(c_255,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_259,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_255,c_6])).

tff(c_274,plain,(
    ! [B_131,A_132] :
      ( B_131 = A_132
      | ~ r1_tarski(B_131,A_132)
      | ~ r1_tarski(A_132,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_279,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_259,c_274])).

tff(c_284,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_310,plain,(
    ! [C_149,A_150,B_151] :
      ( m1_subset_1(C_149,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m2_orders_2(C_149,A_150,B_151)
      | ~ m1_orders_1(B_151,k1_orders_1(u1_struct_0(A_150)))
      | ~ l1_orders_2(A_150)
      | ~ v5_orders_2(A_150)
      | ~ v4_orders_2(A_150)
      | ~ v3_orders_2(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_314,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_310])).

tff(c_321,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_314])).

tff(c_322,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_321])).

tff(c_16,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_254,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_354,plain,(
    ! [C_162,A_163,D_164,B_165] :
      ( m1_orders_2(C_162,A_163,D_164)
      | m1_orders_2(D_164,A_163,C_162)
      | D_164 = C_162
      | ~ m2_orders_2(D_164,A_163,B_165)
      | ~ m2_orders_2(C_162,A_163,B_165)
      | ~ m1_orders_1(B_165,k1_orders_1(u1_struct_0(A_163)))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163)
      | ~ v4_orders_2(A_163)
      | ~ v3_orders_2(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_356,plain,(
    ! [C_162] :
      ( m1_orders_2(C_162,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_162)
      | C_162 = '#skF_4'
      | ~ m2_orders_2(C_162,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_354])).

tff(c_361,plain,(
    ! [C_162] :
      ( m1_orders_2(C_162,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_162)
      | C_162 = '#skF_4'
      | ~ m2_orders_2(C_162,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_356])).

tff(c_367,plain,(
    ! [C_166] :
      ( m1_orders_2(C_166,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_166)
      | C_166 = '#skF_4'
      | ~ m2_orders_2(C_166,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_361])).

tff(c_373,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_367])).

tff(c_378,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_373])).

tff(c_391,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_396,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_284])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_396])).

tff(c_406,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_30,plain,(
    ! [C_28,B_26,A_22] :
      ( r1_tarski(C_28,B_26)
      | ~ m1_orders_2(C_28,A_22,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22)
      | ~ v4_orders_2(A_22)
      | ~ v3_orders_2(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_413,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_406,c_30])).

tff(c_424,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_322,c_413])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_284,c_424])).

tff(c_427,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_431,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_255])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.37  
% 2.80/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.37  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.80/1.37  
% 2.80/1.37  %Foreground sorts:
% 2.80/1.37  
% 2.80/1.37  
% 2.80/1.37  %Background operators:
% 2.80/1.37  
% 2.80/1.37  
% 2.80/1.37  %Foreground operators:
% 2.80/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.80/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.37  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.80/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.37  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.80/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.37  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.80/1.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.80/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.37  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.80/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.80/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.80/1.37  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.80/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.37  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.80/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.37  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.80/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.37  
% 2.80/1.39  tff(f_36, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.80/1.39  tff(f_211, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 2.80/1.39  tff(f_95, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.80/1.39  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.80/1.39  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.80/1.39  tff(f_139, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 2.80/1.39  tff(f_158, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.80/1.39  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.80/1.39  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.80/1.39  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.80/1.39  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.39  tff(f_186, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 2.80/1.39  tff(c_10, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.80/1.39  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_177, plain, (![C_109, A_110, B_111]: (m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~m2_orders_2(C_109, A_110, B_111) | ~m1_orders_1(B_111, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.80/1.39  tff(c_179, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_177])).
% 2.80/1.39  tff(c_182, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_179])).
% 2.80/1.39  tff(c_183, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_182])).
% 2.80/1.39  tff(c_70, plain, (![A_74, B_75]: (r2_xboole_0(A_74, B_75) | B_75=A_74 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.39  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_68, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 2.80/1.39  tff(c_81, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_68])).
% 2.80/1.39  tff(c_87, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_81])).
% 2.80/1.39  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_69, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_62])).
% 2.80/1.39  tff(c_118, plain, (![C_88, B_89, A_90]: (r1_tarski(C_88, B_89) | ~m1_orders_2(C_88, A_90, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.80/1.39  tff(c_120, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_69, c_118])).
% 2.80/1.39  tff(c_123, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_120])).
% 2.80/1.39  tff(c_124, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_87, c_123])).
% 2.80/1.39  tff(c_125, plain, (![C_91, A_92, B_93]: (m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~m2_orders_2(C_91, A_92, B_93) | ~m1_orders_1(B_93, k1_orders_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.80/1.39  tff(c_127, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_125])).
% 2.80/1.39  tff(c_132, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_127])).
% 2.80/1.39  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_124, c_132])).
% 2.80/1.39  tff(c_135, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_81])).
% 2.80/1.39  tff(c_137, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_69])).
% 2.80/1.39  tff(c_205, plain, (![C_119, A_120, B_121]: (~m1_orders_2(C_119, A_120, B_121) | ~m1_orders_2(B_121, A_120, C_119) | k1_xboole_0=B_121 | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.80/1.39  tff(c_207, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_137, c_205])).
% 2.80/1.39  tff(c_210, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_183, c_137, c_207])).
% 2.80/1.39  tff(c_211, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_210])).
% 2.80/1.39  tff(c_199, plain, (![B_116, A_117, C_118]: (r2_hidden(k1_funct_1(B_116, u1_struct_0(A_117)), C_118) | ~m2_orders_2(C_118, A_117, B_116) | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.80/1.39  tff(c_18, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.80/1.39  tff(c_153, plain, (![C_96, B_97, A_98]: (~v1_xboole_0(C_96) | ~m1_subset_1(B_97, k1_zfmisc_1(C_96)) | ~r2_hidden(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.39  tff(c_156, plain, (![A_7, A_98]: (~v1_xboole_0(A_7) | ~r2_hidden(A_98, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_153])).
% 2.80/1.39  tff(c_161, plain, (![A_98]: (~r2_hidden(A_98, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_156])).
% 2.80/1.39  tff(c_204, plain, (![A_117, B_116]: (~m2_orders_2(k1_xboole_0, A_117, B_116) | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_199, c_161])).
% 2.80/1.39  tff(c_235, plain, (![A_124, B_125]: (~m2_orders_2('#skF_4', A_124, B_125) | ~m1_orders_1(B_125, k1_orders_1(u1_struct_0(A_124))) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_204])).
% 2.80/1.39  tff(c_238, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2') | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_235])).
% 2.80/1.39  tff(c_241, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_40, c_238])).
% 2.80/1.39  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_241])).
% 2.80/1.39  tff(c_244, plain, (![A_7]: (~v1_xboole_0(A_7))), inference(splitRight, [status(thm)], [c_156])).
% 2.80/1.39  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.39  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_8])).
% 2.80/1.39  tff(c_255, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.80/1.39  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.39  tff(c_259, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_255, c_6])).
% 2.80/1.39  tff(c_274, plain, (![B_131, A_132]: (B_131=A_132 | ~r1_tarski(B_131, A_132) | ~r1_tarski(A_132, B_131))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.39  tff(c_279, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_259, c_274])).
% 2.80/1.39  tff(c_284, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_279])).
% 2.80/1.39  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.80/1.39  tff(c_310, plain, (![C_149, A_150, B_151]: (m1_subset_1(C_149, k1_zfmisc_1(u1_struct_0(A_150))) | ~m2_orders_2(C_149, A_150, B_151) | ~m1_orders_1(B_151, k1_orders_1(u1_struct_0(A_150))) | ~l1_orders_2(A_150) | ~v5_orders_2(A_150) | ~v4_orders_2(A_150) | ~v3_orders_2(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.80/1.39  tff(c_314, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_310])).
% 2.80/1.39  tff(c_321, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_314])).
% 2.80/1.39  tff(c_322, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_321])).
% 2.80/1.39  tff(c_16, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.39  tff(c_254, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.80/1.39  tff(c_354, plain, (![C_162, A_163, D_164, B_165]: (m1_orders_2(C_162, A_163, D_164) | m1_orders_2(D_164, A_163, C_162) | D_164=C_162 | ~m2_orders_2(D_164, A_163, B_165) | ~m2_orders_2(C_162, A_163, B_165) | ~m1_orders_1(B_165, k1_orders_1(u1_struct_0(A_163))) | ~l1_orders_2(A_163) | ~v5_orders_2(A_163) | ~v4_orders_2(A_163) | ~v3_orders_2(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.80/1.39  tff(c_356, plain, (![C_162]: (m1_orders_2(C_162, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_162) | C_162='#skF_4' | ~m2_orders_2(C_162, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_354])).
% 2.80/1.39  tff(c_361, plain, (![C_162]: (m1_orders_2(C_162, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_162) | C_162='#skF_4' | ~m2_orders_2(C_162, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_356])).
% 2.80/1.39  tff(c_367, plain, (![C_166]: (m1_orders_2(C_166, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_166) | C_166='#skF_4' | ~m2_orders_2(C_166, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_361])).
% 2.80/1.39  tff(c_373, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_367])).
% 2.80/1.39  tff(c_378, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_254, c_373])).
% 2.80/1.39  tff(c_391, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_378])).
% 2.80/1.39  tff(c_396, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_284])).
% 2.80/1.39  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_396])).
% 2.80/1.39  tff(c_406, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_378])).
% 2.80/1.39  tff(c_30, plain, (![C_28, B_26, A_22]: (r1_tarski(C_28, B_26) | ~m1_orders_2(C_28, A_22, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_orders_2(A_22) | ~v5_orders_2(A_22) | ~v4_orders_2(A_22) | ~v3_orders_2(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.80/1.39  tff(c_413, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_406, c_30])).
% 2.80/1.39  tff(c_424, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_322, c_413])).
% 2.80/1.39  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_284, c_424])).
% 2.80/1.39  tff(c_427, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_279])).
% 2.80/1.39  tff(c_431, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_255])).
% 2.80/1.39  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_431])).
% 2.80/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.39  
% 2.80/1.39  Inference rules
% 2.80/1.39  ----------------------
% 2.80/1.39  #Ref     : 0
% 2.80/1.39  #Sup     : 57
% 2.80/1.39  #Fact    : 0
% 2.80/1.39  #Define  : 0
% 2.80/1.39  #Split   : 10
% 2.80/1.39  #Chain   : 0
% 2.80/1.39  #Close   : 0
% 2.80/1.39  
% 2.80/1.39  Ordering : KBO
% 2.80/1.39  
% 2.80/1.39  Simplification rules
% 2.80/1.39  ----------------------
% 2.80/1.39  #Subsume      : 13
% 2.80/1.39  #Demod        : 145
% 2.80/1.39  #Tautology    : 26
% 2.80/1.39  #SimpNegUnit  : 26
% 2.80/1.39  #BackRed      : 21
% 2.80/1.39  
% 2.80/1.39  #Partial instantiations: 0
% 2.80/1.39  #Strategies tried      : 1
% 2.80/1.39  
% 2.80/1.39  Timing (in seconds)
% 2.80/1.39  ----------------------
% 2.80/1.40  Preprocessing        : 0.33
% 2.80/1.40  Parsing              : 0.19
% 2.80/1.40  CNF conversion       : 0.03
% 2.80/1.40  Main loop            : 0.28
% 2.80/1.40  Inferencing          : 0.10
% 2.80/1.40  Reduction            : 0.09
% 2.80/1.40  Demodulation         : 0.06
% 2.80/1.40  BG Simplification    : 0.02
% 2.80/1.40  Subsumption          : 0.05
% 2.80/1.40  Abstraction          : 0.01
% 2.80/1.40  MUC search           : 0.00
% 2.80/1.40  Cooper               : 0.00
% 2.80/1.40  Total                : 0.65
% 2.80/1.40  Index Insertion      : 0.00
% 2.80/1.40  Index Deletion       : 0.00
% 2.80/1.40  Index Matching       : 0.00
% 2.80/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
