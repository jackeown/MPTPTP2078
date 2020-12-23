%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:00 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 290 expanded)
%              Number of leaves         :   35 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  290 (1236 expanded)
%              Number of equality atoms :   21 (  46 expanded)
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

tff(f_199,negated_conjecture,(
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

tff(f_83,axiom,(
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

tff(f_102,axiom,(
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
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,C)
                  & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_146,axiom,(
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

tff(f_174,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_44,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_42,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_40,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_34,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_38,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_166,plain,(
    ! [C_90,A_91,B_92] :
      ( m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m2_orders_2(C_90,A_91,B_92)
      | ~ m1_orders_1(B_92,k1_orders_1(u1_struct_0(A_91)))
      | ~ l1_orders_2(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v4_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_168,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_166])).

tff(c_171,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_168])).

tff(c_172,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_171])).

tff(c_126,plain,(
    ! [C_81,A_82,B_83] :
      ( m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m2_orders_2(C_81,A_82,B_83)
      | ~ m1_orders_1(B_83,k1_orders_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_130,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_126])).

tff(c_137,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_130])).

tff(c_138,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_137])).

tff(c_88,plain,(
    ! [A_73,B_74] :
      ( r2_xboole_0(A_73,B_74)
      | B_74 = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

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
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_64,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_56])).

tff(c_119,plain,(
    ! [C_78,B_79,A_80] :
      ( r1_tarski(C_78,B_79)
      | ~ m1_orders_2(C_78,A_80,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_121,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_119])).

tff(c_124,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_121])).

tff(c_125,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_105,c_124])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_125])).

tff(c_141,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_143,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64])).

tff(c_185,plain,(
    ! [C_99,A_100,B_101] :
      ( ~ m1_orders_2(C_99,A_100,B_101)
      | ~ m1_orders_2(B_101,A_100,C_99)
      | k1_xboole_0 = B_101
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_orders_2(A_100)
      | ~ v5_orders_2(A_100)
      | ~ v4_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_187,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_143,c_185])).

tff(c_190,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_172,c_143,c_187])).

tff(c_191,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_190])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_194,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_14])).

tff(c_180,plain,(
    ! [B_96,A_97,C_98] :
      ( r2_hidden(k1_funct_1(B_96,u1_struct_0(A_97)),C_98)
      | ~ m2_orders_2(C_98,A_97,B_96)
      | ~ m1_orders_1(B_96,k1_orders_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_216,plain,(
    ! [C_104,B_105,A_106] :
      ( ~ r1_tarski(C_104,k1_funct_1(B_105,u1_struct_0(A_106)))
      | ~ m2_orders_2(C_104,A_106,B_105)
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_106)))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_180,c_16])).

tff(c_241,plain,(
    ! [A_112,B_113] :
      ( ~ m2_orders_2('#skF_4',A_112,B_113)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_194,c_216])).

tff(c_244,plain,
    ( ~ m2_orders_2('#skF_4','#skF_1','#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_241])).

tff(c_247,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_244])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_247])).

tff(c_251,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_255,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_251,c_6])).

tff(c_257,plain,(
    ! [B_114,A_115] :
      ( B_114 = A_115
      | ~ r1_tarski(B_114,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_264,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_257])).

tff(c_283,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_36,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_311,plain,(
    ! [C_125,A_126,B_127] :
      ( m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m2_orders_2(C_125,A_126,B_127)
      | ~ m1_orders_1(B_127,k1_orders_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_313,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_311])).

tff(c_318,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_313])).

tff(c_319,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_318])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_250,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_351,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_353,plain,(
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
    inference(resolution,[status(thm)],[c_36,c_351])).

tff(c_358,plain,(
    ! [C_144] :
      ( m1_orders_2(C_144,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_144)
      | C_144 = '#skF_3'
      | ~ m2_orders_2(C_144,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_353])).

tff(c_364,plain,(
    ! [C_148] :
      ( m1_orders_2(C_148,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_148)
      | C_148 = '#skF_3'
      | ~ m2_orders_2(C_148,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_358])).

tff(c_370,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_364])).

tff(c_375,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_370])).

tff(c_376,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_380,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_283])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_380])).

tff(c_390,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_24,plain,(
    ! [C_22,B_20,A_16] :
      ( r1_tarski(C_22,B_20)
      | ~ m1_orders_2(C_22,A_16,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_orders_2(A_16)
      | ~ v5_orders_2(A_16)
      | ~ v4_orders_2(A_16)
      | ~ v3_orders_2(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_400,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_390,c_24])).

tff(c_415,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_319,c_400])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_283,c_415])).

tff(c_418,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_422,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_251])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.46  
% 2.47/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.46  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.47/1.46  
% 2.47/1.46  %Foreground sorts:
% 2.47/1.46  
% 2.47/1.46  
% 2.47/1.46  %Background operators:
% 2.47/1.46  
% 2.47/1.46  
% 2.47/1.46  %Foreground operators:
% 2.47/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.47/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.46  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.47/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.46  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.47/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.47/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.47/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.46  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.47/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.47/1.46  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.47/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.46  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.47/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.46  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.47/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.46  
% 2.87/1.48  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.87/1.48  tff(f_199, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.87/1.48  tff(f_83, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.87/1.48  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.87/1.48  tff(f_127, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.87/1.48  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.87/1.48  tff(f_146, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.87/1.48  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.87/1.48  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.87/1.48  tff(f_174, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.87/1.48  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.48  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_46, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_44, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_42, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_40, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_34, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_38, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_166, plain, (![C_90, A_91, B_92]: (m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~m2_orders_2(C_90, A_91, B_92) | ~m1_orders_1(B_92, k1_orders_1(u1_struct_0(A_91))) | ~l1_orders_2(A_91) | ~v5_orders_2(A_91) | ~v4_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.48  tff(c_168, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_166])).
% 2.87/1.48  tff(c_171, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_168])).
% 2.87/1.48  tff(c_172, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_171])).
% 2.87/1.48  tff(c_126, plain, (![C_81, A_82, B_83]: (m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~m2_orders_2(C_81, A_82, B_83) | ~m1_orders_1(B_83, k1_orders_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.48  tff(c_130, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_126])).
% 2.87/1.48  tff(c_137, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_130])).
% 2.87/1.48  tff(c_138, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_137])).
% 2.87/1.48  tff(c_88, plain, (![A_73, B_74]: (r2_xboole_0(A_73, B_74) | B_74=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.48  tff(c_50, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_63, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.87/1.48  tff(c_99, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_63])).
% 2.87/1.48  tff(c_105, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_99])).
% 2.87/1.48  tff(c_56, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_64, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_63, c_56])).
% 2.87/1.48  tff(c_119, plain, (![C_78, B_79, A_80]: (r1_tarski(C_78, B_79) | ~m1_orders_2(C_78, A_80, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.87/1.48  tff(c_121, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_119])).
% 2.87/1.48  tff(c_124, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_121])).
% 2.87/1.48  tff(c_125, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_105, c_124])).
% 2.87/1.48  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_125])).
% 2.87/1.48  tff(c_141, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_99])).
% 2.87/1.48  tff(c_143, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_64])).
% 2.87/1.48  tff(c_185, plain, (![C_99, A_100, B_101]: (~m1_orders_2(C_99, A_100, B_101) | ~m1_orders_2(B_101, A_100, C_99) | k1_xboole_0=B_101 | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_orders_2(A_100) | ~v5_orders_2(A_100) | ~v4_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.87/1.48  tff(c_187, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_143, c_185])).
% 2.87/1.48  tff(c_190, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_172, c_143, c_187])).
% 2.87/1.48  tff(c_191, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_190])).
% 2.87/1.48  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.48  tff(c_194, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_14])).
% 2.87/1.48  tff(c_180, plain, (![B_96, A_97, C_98]: (r2_hidden(k1_funct_1(B_96, u1_struct_0(A_97)), C_98) | ~m2_orders_2(C_98, A_97, B_96) | ~m1_orders_1(B_96, k1_orders_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.87/1.48  tff(c_16, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.48  tff(c_216, plain, (![C_104, B_105, A_106]: (~r1_tarski(C_104, k1_funct_1(B_105, u1_struct_0(A_106))) | ~m2_orders_2(C_104, A_106, B_105) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_106))) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_180, c_16])).
% 2.87/1.48  tff(c_241, plain, (![A_112, B_113]: (~m2_orders_2('#skF_4', A_112, B_113) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_194, c_216])).
% 2.87/1.48  tff(c_244, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2') | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_241])).
% 2.87/1.48  tff(c_247, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_244])).
% 2.87/1.48  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_247])).
% 2.87/1.48  tff(c_251, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.87/1.48  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.48  tff(c_255, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_251, c_6])).
% 2.87/1.48  tff(c_257, plain, (![B_114, A_115]: (B_114=A_115 | ~r1_tarski(B_114, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.48  tff(c_264, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_255, c_257])).
% 2.87/1.48  tff(c_283, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_264])).
% 2.87/1.48  tff(c_36, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.87/1.48  tff(c_311, plain, (![C_125, A_126, B_127]: (m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m2_orders_2(C_125, A_126, B_127) | ~m1_orders_1(B_127, k1_orders_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.48  tff(c_313, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_311])).
% 2.87/1.48  tff(c_318, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_313])).
% 2.87/1.48  tff(c_319, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_318])).
% 2.87/1.48  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.48  tff(c_250, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.87/1.48  tff(c_351, plain, (![C_144, A_145, D_146, B_147]: (m1_orders_2(C_144, A_145, D_146) | m1_orders_2(D_146, A_145, C_144) | D_146=C_144 | ~m2_orders_2(D_146, A_145, B_147) | ~m2_orders_2(C_144, A_145, B_147) | ~m1_orders_1(B_147, k1_orders_1(u1_struct_0(A_145))) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.87/1.48  tff(c_353, plain, (![C_144]: (m1_orders_2(C_144, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_144) | C_144='#skF_3' | ~m2_orders_2(C_144, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_351])).
% 2.87/1.48  tff(c_358, plain, (![C_144]: (m1_orders_2(C_144, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_144) | C_144='#skF_3' | ~m2_orders_2(C_144, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_353])).
% 2.87/1.48  tff(c_364, plain, (![C_148]: (m1_orders_2(C_148, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_148) | C_148='#skF_3' | ~m2_orders_2(C_148, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_358])).
% 2.87/1.48  tff(c_370, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_34, c_364])).
% 2.87/1.48  tff(c_375, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_250, c_370])).
% 2.87/1.48  tff(c_376, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_375])).
% 2.87/1.48  tff(c_380, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_283])).
% 2.87/1.48  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_380])).
% 2.87/1.48  tff(c_390, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_375])).
% 2.87/1.48  tff(c_24, plain, (![C_22, B_20, A_16]: (r1_tarski(C_22, B_20) | ~m1_orders_2(C_22, A_16, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_orders_2(A_16) | ~v5_orders_2(A_16) | ~v4_orders_2(A_16) | ~v3_orders_2(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.87/1.48  tff(c_400, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_390, c_24])).
% 2.87/1.48  tff(c_415, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_319, c_400])).
% 2.87/1.48  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_283, c_415])).
% 2.87/1.48  tff(c_418, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_264])).
% 2.87/1.48  tff(c_422, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_251])).
% 2.87/1.48  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_422])).
% 2.87/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.48  
% 2.87/1.48  Inference rules
% 2.87/1.48  ----------------------
% 2.87/1.48  #Ref     : 0
% 2.87/1.48  #Sup     : 54
% 2.87/1.48  #Fact    : 0
% 2.87/1.48  #Define  : 0
% 2.87/1.48  #Split   : 4
% 2.87/1.48  #Chain   : 0
% 2.87/1.48  #Close   : 0
% 2.87/1.48  
% 2.87/1.48  Ordering : KBO
% 2.87/1.48  
% 2.87/1.48  Simplification rules
% 2.87/1.48  ----------------------
% 2.87/1.48  #Subsume      : 4
% 2.87/1.48  #Demod        : 152
% 2.87/1.48  #Tautology    : 30
% 2.87/1.48  #SimpNegUnit  : 26
% 2.87/1.48  #BackRed      : 18
% 2.87/1.48  
% 2.87/1.48  #Partial instantiations: 0
% 2.87/1.48  #Strategies tried      : 1
% 2.87/1.48  
% 2.87/1.48  Timing (in seconds)
% 2.87/1.48  ----------------------
% 2.87/1.49  Preprocessing        : 0.38
% 2.87/1.49  Parsing              : 0.20
% 2.87/1.49  CNF conversion       : 0.03
% 2.87/1.49  Main loop            : 0.28
% 2.87/1.49  Inferencing          : 0.11
% 2.87/1.49  Reduction            : 0.09
% 2.87/1.49  Demodulation         : 0.07
% 2.87/1.49  BG Simplification    : 0.02
% 2.87/1.49  Subsumption          : 0.05
% 2.87/1.49  Abstraction          : 0.01
% 2.87/1.49  MUC search           : 0.00
% 2.87/1.49  Cooper               : 0.00
% 2.87/1.49  Total                : 0.70
% 2.87/1.49  Index Insertion      : 0.00
% 2.87/1.49  Index Deletion       : 0.00
% 2.87/1.49  Index Matching       : 0.00
% 2.87/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
