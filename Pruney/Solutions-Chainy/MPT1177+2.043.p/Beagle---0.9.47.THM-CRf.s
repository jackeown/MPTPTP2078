%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:01 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 306 expanded)
%              Number of leaves         :   35 ( 127 expanded)
%              Depth                    :   14
%              Number of atoms          :  290 (1321 expanded)
%              Number of equality atoms :   23 (  54 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_182,negated_conjecture,(
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

tff(f_84,axiom,(
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

tff(f_65,axiom,(
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
         => ( ~ ( B != k1_xboole_0
                & m1_orders_2(B,A,B) )
            & ~ ( ~ m1_orders_2(B,A,B)
                & B = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_157,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_46,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_44,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_42,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_40,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_34,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_38,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_88,plain,(
    ! [A_65,B_66] :
      ( r2_xboole_0(A_65,B_66)
      | B_66 = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_63,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_99,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_63])).

tff(c_105,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_56,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_64,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_56])).

tff(c_108,plain,(
    ! [C_70,B_71,A_72] :
      ( r1_tarski(C_70,B_71)
      | ~ m1_orders_2(C_70,A_72,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_110,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_108])).

tff(c_113,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_110])).

tff(c_114,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_105,c_113])).

tff(c_128,plain,(
    ! [C_76,A_77,B_78] :
      ( m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m2_orders_2(C_76,A_77,B_78)
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_132,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_139,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_132])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_114,c_139])).

tff(c_142,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_144,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_64])).

tff(c_154,plain,(
    ! [B_80,A_81] :
      ( ~ m1_orders_2(B_80,A_81,B_80)
      | k1_xboole_0 = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_orders_2(A_81)
      | ~ v5_orders_2(A_81)
      | ~ v4_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_156,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_144,c_154])).

tff(c_159,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_156])).

tff(c_160,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_159])).

tff(c_161,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_176,plain,(
    ! [C_88,A_89,B_90] :
      ( m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m2_orders_2(C_88,A_89,B_90)
      | ~ m1_orders_1(B_90,k1_orders_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_178,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_176])).

tff(c_181,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_178])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_161,c_181])).

tff(c_184,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_189,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_14])).

tff(c_248,plain,(
    ! [B_105,A_106,C_107] :
      ( r2_hidden(k1_funct_1(B_105,u1_struct_0(A_106)),C_107)
      | ~ m2_orders_2(C_107,A_106,B_105)
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_106)))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_253,plain,(
    ! [C_108,B_109,A_110] :
      ( ~ r1_tarski(C_108,k1_funct_1(B_109,u1_struct_0(A_110)))
      | ~ m2_orders_2(C_108,A_110,B_109)
      | ~ m1_orders_1(B_109,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_248,c_16])).

tff(c_264,plain,(
    ! [A_111,B_112] :
      ( ~ m2_orders_2('#skF_4',A_111,B_112)
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0(A_111)))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_189,c_253])).

tff(c_267,plain,
    ( ~ m2_orders_2('#skF_4','#skF_1','#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_264])).

tff(c_270,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_267])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_270])).

tff(c_274,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_278,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_274,c_6])).

tff(c_281,plain,(
    ! [B_113,A_114] :
      ( B_113 = A_114
      | ~ r1_tarski(B_113,A_114)
      | ~ r1_tarski(A_114,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_288,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_281])).

tff(c_294,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_36,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_337,plain,(
    ! [C_127,A_128,B_129] :
      ( m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m2_orders_2(C_127,A_128,B_129)
      | ~ m1_orders_1(B_129,k1_orders_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_339,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_337])).

tff(c_344,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_339])).

tff(c_345,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_344])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_273,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_376,plain,(
    ! [C_144,A_145,D_146,B_147] :
      ( m1_orders_2(C_144,A_145,D_146)
      | m1_orders_2(D_146,A_145,C_144)
      | D_146 = C_144
      | ~ m2_orders_2(D_146,A_145,B_147)
      | ~ m2_orders_2(C_144,A_145,B_147)
      | ~ m1_orders_1(B_147,k1_orders_1(u1_struct_0(A_145)))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_378,plain,(
    ! [C_144] :
      ( m1_orders_2(C_144,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_144)
      | C_144 = '#skF_3'
      | ~ m2_orders_2(C_144,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_376])).

tff(c_383,plain,(
    ! [C_144] :
      ( m1_orders_2(C_144,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_144)
      | C_144 = '#skF_3'
      | ~ m2_orders_2(C_144,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_378])).

tff(c_389,plain,(
    ! [C_148] :
      ( m1_orders_2(C_148,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_148)
      | C_148 = '#skF_3'
      | ~ m2_orders_2(C_148,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_383])).

tff(c_395,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_389])).

tff(c_400,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_395])).

tff(c_401,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_400])).

tff(c_405,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_294])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_405])).

tff(c_415,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_400])).

tff(c_22,plain,(
    ! [C_18,B_16,A_12] :
      ( r1_tarski(C_18,B_16)
      | ~ m1_orders_2(C_18,A_12,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12)
      | ~ v4_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_420,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_415,c_22])).

tff(c_427,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_345,c_420])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_294,c_427])).

tff(c_430,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_434,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_274])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:48:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.40  
% 2.60/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.41  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.60/1.41  
% 2.60/1.41  %Foreground sorts:
% 2.60/1.41  
% 2.60/1.41  
% 2.60/1.41  %Background operators:
% 2.60/1.41  
% 2.60/1.41  
% 2.60/1.41  %Foreground operators:
% 2.60/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.60/1.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.60/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.41  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.60/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.41  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.60/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.60/1.41  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.60/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.60/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.60/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.60/1.41  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.60/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.41  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.60/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.41  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.60/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.41  
% 2.60/1.43  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.60/1.43  tff(f_182, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.60/1.43  tff(f_84, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.60/1.43  tff(f_65, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.60/1.43  tff(f_110, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_orders_2)).
% 2.60/1.43  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.60/1.43  tff(f_129, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.60/1.43  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.60/1.43  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.60/1.43  tff(f_157, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.60/1.43  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.43  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_46, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_44, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_42, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_40, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_34, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_38, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_88, plain, (![A_65, B_66]: (r2_xboole_0(A_65, B_66) | B_66=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.43  tff(c_50, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_63, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.60/1.43  tff(c_99, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_63])).
% 2.60/1.43  tff(c_105, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_99])).
% 2.60/1.43  tff(c_56, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_64, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_63, c_56])).
% 2.60/1.43  tff(c_108, plain, (![C_70, B_71, A_72]: (r1_tarski(C_70, B_71) | ~m1_orders_2(C_70, A_72, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.43  tff(c_110, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_108])).
% 2.60/1.43  tff(c_113, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_110])).
% 2.60/1.43  tff(c_114, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_105, c_113])).
% 2.60/1.43  tff(c_128, plain, (![C_76, A_77, B_78]: (m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~m2_orders_2(C_76, A_77, B_78) | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.43  tff(c_132, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_128])).
% 2.60/1.43  tff(c_139, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_132])).
% 2.60/1.43  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_114, c_139])).
% 2.60/1.43  tff(c_142, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_99])).
% 2.60/1.43  tff(c_144, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_64])).
% 2.60/1.43  tff(c_154, plain, (![B_80, A_81]: (~m1_orders_2(B_80, A_81, B_80) | k1_xboole_0=B_80 | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_orders_2(A_81) | ~v5_orders_2(A_81) | ~v4_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.60/1.43  tff(c_156, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_144, c_154])).
% 2.60/1.43  tff(c_159, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_156])).
% 2.60/1.43  tff(c_160, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_159])).
% 2.60/1.43  tff(c_161, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_160])).
% 2.60/1.43  tff(c_176, plain, (![C_88, A_89, B_90]: (m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~m2_orders_2(C_88, A_89, B_90) | ~m1_orders_1(B_90, k1_orders_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.43  tff(c_178, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_176])).
% 2.60/1.43  tff(c_181, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_178])).
% 2.60/1.43  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_161, c_181])).
% 2.60/1.43  tff(c_184, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_160])).
% 2.60/1.43  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.60/1.43  tff(c_189, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_14])).
% 2.60/1.43  tff(c_248, plain, (![B_105, A_106, C_107]: (r2_hidden(k1_funct_1(B_105, u1_struct_0(A_106)), C_107) | ~m2_orders_2(C_107, A_106, B_105) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_106))) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.60/1.43  tff(c_16, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.43  tff(c_253, plain, (![C_108, B_109, A_110]: (~r1_tarski(C_108, k1_funct_1(B_109, u1_struct_0(A_110))) | ~m2_orders_2(C_108, A_110, B_109) | ~m1_orders_1(B_109, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_248, c_16])).
% 2.60/1.43  tff(c_264, plain, (![A_111, B_112]: (~m2_orders_2('#skF_4', A_111, B_112) | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0(A_111))) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_189, c_253])).
% 2.60/1.43  tff(c_267, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2') | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_264])).
% 2.60/1.43  tff(c_270, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_267])).
% 2.60/1.43  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_270])).
% 2.60/1.43  tff(c_274, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.60/1.43  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.43  tff(c_278, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_274, c_6])).
% 2.60/1.43  tff(c_281, plain, (![B_113, A_114]: (B_113=A_114 | ~r1_tarski(B_113, A_114) | ~r1_tarski(A_114, B_113))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.43  tff(c_288, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_278, c_281])).
% 2.60/1.43  tff(c_294, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_288])).
% 2.60/1.43  tff(c_36, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.60/1.43  tff(c_337, plain, (![C_127, A_128, B_129]: (m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~m2_orders_2(C_127, A_128, B_129) | ~m1_orders_1(B_129, k1_orders_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.43  tff(c_339, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_337])).
% 2.60/1.43  tff(c_344, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_339])).
% 2.60/1.43  tff(c_345, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_344])).
% 2.60/1.43  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.43  tff(c_273, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.60/1.43  tff(c_376, plain, (![C_144, A_145, D_146, B_147]: (m1_orders_2(C_144, A_145, D_146) | m1_orders_2(D_146, A_145, C_144) | D_146=C_144 | ~m2_orders_2(D_146, A_145, B_147) | ~m2_orders_2(C_144, A_145, B_147) | ~m1_orders_1(B_147, k1_orders_1(u1_struct_0(A_145))) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.60/1.43  tff(c_378, plain, (![C_144]: (m1_orders_2(C_144, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_144) | C_144='#skF_3' | ~m2_orders_2(C_144, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_376])).
% 2.60/1.43  tff(c_383, plain, (![C_144]: (m1_orders_2(C_144, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_144) | C_144='#skF_3' | ~m2_orders_2(C_144, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_378])).
% 2.60/1.43  tff(c_389, plain, (![C_148]: (m1_orders_2(C_148, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_148) | C_148='#skF_3' | ~m2_orders_2(C_148, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_383])).
% 2.60/1.43  tff(c_395, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_34, c_389])).
% 2.60/1.43  tff(c_400, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_273, c_395])).
% 2.60/1.43  tff(c_401, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_400])).
% 2.60/1.43  tff(c_405, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_294])).
% 2.60/1.43  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_405])).
% 2.60/1.43  tff(c_415, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_400])).
% 2.60/1.43  tff(c_22, plain, (![C_18, B_16, A_12]: (r1_tarski(C_18, B_16) | ~m1_orders_2(C_18, A_12, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12) | ~v4_orders_2(A_12) | ~v3_orders_2(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.43  tff(c_420, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_415, c_22])).
% 2.60/1.43  tff(c_427, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_345, c_420])).
% 2.60/1.43  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_294, c_427])).
% 2.60/1.43  tff(c_430, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_288])).
% 2.60/1.43  tff(c_434, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_274])).
% 2.60/1.43  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_434])).
% 2.60/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.43  
% 2.60/1.43  Inference rules
% 2.60/1.43  ----------------------
% 2.60/1.43  #Ref     : 0
% 2.60/1.43  #Sup     : 54
% 2.60/1.43  #Fact    : 0
% 2.60/1.43  #Define  : 0
% 2.60/1.43  #Split   : 5
% 2.60/1.43  #Chain   : 0
% 2.60/1.43  #Close   : 0
% 2.60/1.43  
% 2.60/1.43  Ordering : KBO
% 2.60/1.43  
% 2.60/1.43  Simplification rules
% 2.60/1.43  ----------------------
% 2.60/1.43  #Subsume      : 3
% 2.60/1.43  #Demod        : 155
% 2.60/1.43  #Tautology    : 31
% 2.60/1.43  #SimpNegUnit  : 28
% 2.60/1.43  #BackRed      : 19
% 2.60/1.43  
% 2.60/1.43  #Partial instantiations: 0
% 2.60/1.43  #Strategies tried      : 1
% 2.60/1.43  
% 2.60/1.43  Timing (in seconds)
% 2.60/1.43  ----------------------
% 2.60/1.43  Preprocessing        : 0.33
% 2.60/1.43  Parsing              : 0.19
% 2.60/1.43  CNF conversion       : 0.03
% 2.60/1.43  Main loop            : 0.27
% 2.60/1.43  Inferencing          : 0.10
% 2.60/1.43  Reduction            : 0.09
% 2.60/1.43  Demodulation         : 0.06
% 2.60/1.43  BG Simplification    : 0.02
% 2.60/1.43  Subsumption          : 0.05
% 2.60/1.43  Abstraction          : 0.01
% 2.60/1.43  MUC search           : 0.00
% 2.60/1.43  Cooper               : 0.00
% 2.60/1.43  Total                : 0.65
% 2.60/1.43  Index Insertion      : 0.00
% 2.60/1.43  Index Deletion       : 0.00
% 2.60/1.43  Index Matching       : 0.00
% 2.60/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
