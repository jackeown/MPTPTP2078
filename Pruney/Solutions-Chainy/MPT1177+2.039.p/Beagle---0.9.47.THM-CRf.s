%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:00 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 263 expanded)
%              Number of leaves         :   34 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  275 (1173 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_203,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

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

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_150,axiom,(
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
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_178,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_34,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_46,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_44,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_42,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_40,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_38,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_167,plain,(
    ! [C_103,A_104,B_105] :
      ( m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m2_orders_2(C_103,A_104,B_105)
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_169,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_167])).

tff(c_172,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_169])).

tff(c_173,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_172])).

tff(c_72,plain,(
    ! [A_80,B_81] :
      ( r2_xboole_0(A_80,B_81)
      | B_81 = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_63,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_86,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_63])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_56,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_64,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_56])).

tff(c_94,plain,(
    ! [C_82,B_83,A_84] :
      ( r1_tarski(C_82,B_83)
      | ~ m1_orders_2(C_82,A_84,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_orders_2(A_84)
      | ~ v5_orders_2(A_84)
      | ~ v4_orders_2(A_84)
      | ~ v3_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_96,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_94])).

tff(c_99,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_96])).

tff(c_100,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_93,c_99])).

tff(c_121,plain,(
    ! [C_91,A_92,B_93] :
      ( m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m2_orders_2(C_91,A_92,B_93)
      | ~ m1_orders_1(B_93,k1_orders_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_125,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_132,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_125])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_100,c_132])).

tff(c_135,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_137,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_64])).

tff(c_185,plain,(
    ! [C_113,A_114,B_115] :
      ( ~ m1_orders_2(C_113,A_114,B_115)
      | ~ m1_orders_2(B_115,A_114,C_113)
      | k1_xboole_0 = B_115
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
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
    inference(resolution,[status(thm)],[c_137,c_185])).

tff(c_190,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_173,c_137,c_187])).

tff(c_191,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_190])).

tff(c_16,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_174,plain,(
    ! [C_106,D_107,A_108,B_109] :
      ( ~ r1_xboole_0(C_106,D_107)
      | ~ m2_orders_2(D_107,A_108,B_109)
      | ~ m2_orders_2(C_106,A_108,B_109)
      | ~ m1_orders_1(B_109,k1_orders_1(u1_struct_0(A_108)))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_178,plain,(
    ! [A_110,B_111,A_112] :
      ( ~ m2_orders_2(k1_xboole_0,A_110,B_111)
      | ~ m2_orders_2(A_112,A_110,B_111)
      | ~ m1_orders_1(B_111,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_180,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_178])).

tff(c_183,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_180])).

tff(c_184,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_183])).

tff(c_193,plain,(
    ~ m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_184])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_193])).

tff(c_200,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( ~ r2_xboole_0(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_200,c_14])).

tff(c_36,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_252,plain,(
    ! [C_126,A_127,B_128] :
      ( m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m2_orders_2(C_126,A_127,B_128)
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_254,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_252])).

tff(c_259,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_254])).

tff(c_260,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_259])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_285,plain,(
    ! [C_146,A_147,D_148,B_149] :
      ( m1_orders_2(C_146,A_147,D_148)
      | m1_orders_2(D_148,A_147,C_146)
      | D_148 = C_146
      | ~ m2_orders_2(D_148,A_147,B_149)
      | ~ m2_orders_2(C_146,A_147,B_149)
      | ~ m1_orders_1(B_149,k1_orders_1(u1_struct_0(A_147)))
      | ~ l1_orders_2(A_147)
      | ~ v5_orders_2(A_147)
      | ~ v4_orders_2(A_147)
      | ~ v3_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_287,plain,(
    ! [C_146] :
      ( m1_orders_2(C_146,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_146)
      | C_146 = '#skF_3'
      | ~ m2_orders_2(C_146,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_285])).

tff(c_292,plain,(
    ! [C_146] :
      ( m1_orders_2(C_146,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_146)
      | C_146 = '#skF_3'
      | ~ m2_orders_2(C_146,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_287])).

tff(c_298,plain,(
    ! [C_150] :
      ( m1_orders_2(C_150,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_150)
      | C_150 = '#skF_3'
      | ~ m2_orders_2(C_150,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_292])).

tff(c_304,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_298])).

tff(c_309,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_304])).

tff(c_310,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_327,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_208])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_327])).

tff(c_336,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_309])).

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

tff(c_345,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_336,c_24])).

tff(c_360,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_260,c_345])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_208,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.30  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.30  
% 2.28/1.30  %Foreground sorts:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Background operators:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Foreground operators:
% 2.28/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.28/1.30  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.30  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.28/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.30  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.28/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.30  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.28/1.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.28/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.30  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.28/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.28/1.30  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.30  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.28/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.30  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.28/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.30  
% 2.62/1.31  tff(f_203, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.62/1.31  tff(f_83, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.62/1.31  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.62/1.31  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.62/1.32  tff(f_127, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.62/1.32  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.62/1.32  tff(f_150, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.62/1.32  tff(f_43, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.62/1.32  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.62/1.32  tff(f_178, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.62/1.32  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_34, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_46, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_44, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_42, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_40, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_38, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_167, plain, (![C_103, A_104, B_105]: (m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~m2_orders_2(C_103, A_104, B_105) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.32  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_167])).
% 2.62/1.32  tff(c_172, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_169])).
% 2.62/1.32  tff(c_173, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_172])).
% 2.62/1.32  tff(c_72, plain, (![A_80, B_81]: (r2_xboole_0(A_80, B_81) | B_81=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.32  tff(c_50, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_63, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.62/1.32  tff(c_86, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_63])).
% 2.62/1.32  tff(c_93, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 2.62/1.32  tff(c_56, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_64, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_63, c_56])).
% 2.62/1.32  tff(c_94, plain, (![C_82, B_83, A_84]: (r1_tarski(C_82, B_83) | ~m1_orders_2(C_82, A_84, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_orders_2(A_84) | ~v5_orders_2(A_84) | ~v4_orders_2(A_84) | ~v3_orders_2(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.62/1.32  tff(c_96, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_94])).
% 2.62/1.32  tff(c_99, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_96])).
% 2.62/1.32  tff(c_100, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_93, c_99])).
% 2.62/1.32  tff(c_121, plain, (![C_91, A_92, B_93]: (m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~m2_orders_2(C_91, A_92, B_93) | ~m1_orders_1(B_93, k1_orders_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.32  tff(c_125, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_121])).
% 2.62/1.32  tff(c_132, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_125])).
% 2.62/1.32  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_100, c_132])).
% 2.62/1.32  tff(c_135, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_86])).
% 2.62/1.32  tff(c_137, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_64])).
% 2.62/1.32  tff(c_185, plain, (![C_113, A_114, B_115]: (~m1_orders_2(C_113, A_114, B_115) | ~m1_orders_2(B_115, A_114, C_113) | k1_xboole_0=B_115 | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.62/1.32  tff(c_187, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_137, c_185])).
% 2.62/1.32  tff(c_190, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_173, c_137, c_187])).
% 2.62/1.32  tff(c_191, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_190])).
% 2.62/1.32  tff(c_16, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.32  tff(c_174, plain, (![C_106, D_107, A_108, B_109]: (~r1_xboole_0(C_106, D_107) | ~m2_orders_2(D_107, A_108, B_109) | ~m2_orders_2(C_106, A_108, B_109) | ~m1_orders_1(B_109, k1_orders_1(u1_struct_0(A_108))) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.62/1.32  tff(c_178, plain, (![A_110, B_111, A_112]: (~m2_orders_2(k1_xboole_0, A_110, B_111) | ~m2_orders_2(A_112, A_110, B_111) | ~m1_orders_1(B_111, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_16, c_174])).
% 2.62/1.32  tff(c_180, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_178])).
% 2.62/1.32  tff(c_183, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_180])).
% 2.62/1.32  tff(c_184, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_183])).
% 2.62/1.32  tff(c_193, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_184])).
% 2.62/1.32  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_193])).
% 2.62/1.32  tff(c_200, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.62/1.32  tff(c_14, plain, (![B_6, A_5]: (~r2_xboole_0(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.32  tff(c_208, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_200, c_14])).
% 2.62/1.32  tff(c_36, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 2.62/1.32  tff(c_252, plain, (![C_126, A_127, B_128]: (m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~m2_orders_2(C_126, A_127, B_128) | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.32  tff(c_254, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_252])).
% 2.62/1.32  tff(c_259, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_254])).
% 2.62/1.32  tff(c_260, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_259])).
% 2.62/1.32  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.62/1.32  tff(c_199, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.62/1.32  tff(c_285, plain, (![C_146, A_147, D_148, B_149]: (m1_orders_2(C_146, A_147, D_148) | m1_orders_2(D_148, A_147, C_146) | D_148=C_146 | ~m2_orders_2(D_148, A_147, B_149) | ~m2_orders_2(C_146, A_147, B_149) | ~m1_orders_1(B_149, k1_orders_1(u1_struct_0(A_147))) | ~l1_orders_2(A_147) | ~v5_orders_2(A_147) | ~v4_orders_2(A_147) | ~v3_orders_2(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.62/1.32  tff(c_287, plain, (![C_146]: (m1_orders_2(C_146, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_146) | C_146='#skF_3' | ~m2_orders_2(C_146, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_285])).
% 2.62/1.32  tff(c_292, plain, (![C_146]: (m1_orders_2(C_146, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_146) | C_146='#skF_3' | ~m2_orders_2(C_146, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_287])).
% 2.62/1.32  tff(c_298, plain, (![C_150]: (m1_orders_2(C_150, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_150) | C_150='#skF_3' | ~m2_orders_2(C_150, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_292])).
% 2.62/1.32  tff(c_304, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_34, c_298])).
% 2.62/1.32  tff(c_309, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_199, c_304])).
% 2.62/1.32  tff(c_310, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_309])).
% 2.62/1.32  tff(c_327, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_208])).
% 2.62/1.32  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_327])).
% 2.62/1.32  tff(c_336, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_309])).
% 2.62/1.32  tff(c_24, plain, (![C_22, B_20, A_16]: (r1_tarski(C_22, B_20) | ~m1_orders_2(C_22, A_16, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_orders_2(A_16) | ~v5_orders_2(A_16) | ~v4_orders_2(A_16) | ~v3_orders_2(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.62/1.32  tff(c_345, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_336, c_24])).
% 2.62/1.32  tff(c_360, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_260, c_345])).
% 2.62/1.32  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_208, c_360])).
% 2.62/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.32  
% 2.62/1.32  Inference rules
% 2.62/1.32  ----------------------
% 2.62/1.32  #Ref     : 0
% 2.62/1.32  #Sup     : 44
% 2.62/1.32  #Fact    : 0
% 2.62/1.32  #Define  : 0
% 2.62/1.32  #Split   : 3
% 2.62/1.32  #Chain   : 0
% 2.62/1.32  #Close   : 0
% 2.62/1.32  
% 2.62/1.32  Ordering : KBO
% 2.62/1.32  
% 2.62/1.32  Simplification rules
% 2.62/1.32  ----------------------
% 2.62/1.32  #Subsume      : 9
% 2.62/1.32  #Demod        : 149
% 2.62/1.32  #Tautology    : 21
% 2.62/1.32  #SimpNegUnit  : 28
% 2.62/1.32  #BackRed      : 15
% 2.62/1.32  
% 2.62/1.32  #Partial instantiations: 0
% 2.62/1.32  #Strategies tried      : 1
% 2.62/1.32  
% 2.62/1.32  Timing (in seconds)
% 2.62/1.32  ----------------------
% 2.62/1.32  Preprocessing        : 0.32
% 2.62/1.32  Parsing              : 0.18
% 2.62/1.32  CNF conversion       : 0.03
% 2.62/1.32  Main loop            : 0.24
% 2.62/1.32  Inferencing          : 0.09
% 2.62/1.32  Reduction            : 0.08
% 2.62/1.32  Demodulation         : 0.06
% 2.62/1.32  BG Simplification    : 0.02
% 2.62/1.32  Subsumption          : 0.04
% 2.62/1.32  Abstraction          : 0.01
% 2.62/1.32  MUC search           : 0.00
% 2.62/1.32  Cooper               : 0.00
% 2.62/1.32  Total                : 0.61
% 2.62/1.32  Index Insertion      : 0.00
% 2.62/1.32  Index Deletion       : 0.00
% 2.62/1.32  Index Matching       : 0.00
% 2.62/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
