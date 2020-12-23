%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:01 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 454 expanded)
%              Number of leaves         :   41 ( 187 expanded)
%              Depth                    :   15
%              Number of atoms          :  306 (2029 expanded)
%              Number of equality atoms :   22 (  68 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k7_subset_1 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_195,negated_conjecture,(
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

tff(f_98,axiom,(
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

tff(f_117,axiom,(
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

tff(f_142,axiom,(
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

tff(f_76,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_xboole_1)).

tff(f_170,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_251,plain,(
    ! [A_137,B_138] :
      ( r2_xboole_0(A_137,B_138)
      | B_138 = A_137
      | ~ r1_tarski(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_42,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_50,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_48,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_46,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_44,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_171,plain,(
    ! [C_112,A_113,B_114] :
      ( v6_orders_2(C_112,A_113)
      | ~ m2_orders_2(C_112,A_113,B_114)
      | ~ m1_orders_1(B_114,k1_orders_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_173,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_171])).

tff(c_176,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_173])).

tff(c_177,plain,(
    v6_orders_2('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_176])).

tff(c_185,plain,(
    ! [C_118,A_119,B_120] :
      ( m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m2_orders_2(C_118,A_119,B_120)
      | ~ m1_orders_1(B_120,k1_orders_1(u1_struct_0(A_119)))
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_187,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_185])).

tff(c_190,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_187])).

tff(c_191,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_190])).

tff(c_67,plain,(
    ! [A_80,B_81] :
      ( r2_xboole_0(A_80,B_81)
      | B_81 = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_62,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_66,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54])).

tff(c_80,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_66])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_119,plain,(
    ! [C_96,B_97,A_98] :
      ( r1_tarski(C_96,B_97)
      | ~ m1_orders_2(C_96,A_98,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_121,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_119])).

tff(c_124,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_121])).

tff(c_125,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_94,c_124])).

tff(c_38,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_126,plain,(
    ! [C_99,A_100,B_101] :
      ( m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m2_orders_2(C_99,A_100,B_101)
      | ~ m1_orders_1(B_101,k1_orders_1(u1_struct_0(A_100)))
      | ~ l1_orders_2(A_100)
      | ~ v5_orders_2(A_100)
      | ~ v4_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_130,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_126])).

tff(c_137,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_130])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_125,c_137])).

tff(c_140,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_143,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_62])).

tff(c_193,plain,(
    ! [C_123,A_124,B_125] :
      ( ~ m1_orders_2(C_123,A_124,B_125)
      | ~ m1_orders_2(B_125,A_124,C_123)
      | k1_xboole_0 = B_125
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_195,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_143,c_193])).

tff(c_198,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_191,c_143,c_195])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_198])).

tff(c_22,plain,(
    ! [A_8,B_20] :
      ( ~ m2_orders_2(k1_xboole_0,A_8,B_20)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ v6_orders_2(k1_xboole_0,A_8)
      | ~ m1_orders_1(B_20,k1_orders_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_216,plain,(
    ! [A_127,B_128] :
      ( ~ m2_orders_2('#skF_4',A_127,B_128)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ v6_orders_2('#skF_4',A_127)
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_199,c_199,c_22])).

tff(c_218,plain,(
    ! [B_128] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_128)
      | ~ v6_orders_2('#skF_4','#skF_2')
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_191,c_216])).

tff(c_221,plain,(
    ! [B_128] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_128)
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_177,c_218])).

tff(c_230,plain,(
    ! [B_132] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_132)
      | ~ m1_orders_1(B_132,k1_orders_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_221])).

tff(c_233,plain,(
    ~ m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_230])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_233])).

tff(c_238,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_247,plain,(
    ! [B_135,A_136] :
      ( ~ r2_xboole_0(B_135,A_136)
      | ~ r2_xboole_0(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_250,plain,(
    ~ r2_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_247])).

tff(c_264,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_251,c_250])).

tff(c_269,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_477,plain,(
    ! [C_178,A_179,B_180] :
      ( m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m2_orders_2(C_178,A_179,B_180)
      | ~ m1_orders_1(B_180,k1_orders_1(u1_struct_0(A_179)))
      | ~ l1_orders_2(A_179)
      | ~ v5_orders_2(A_179)
      | ~ v4_orders_2(A_179)
      | ~ v3_orders_2(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_479,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_477])).

tff(c_484,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_479])).

tff(c_485,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_484])).

tff(c_241,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_54])).

tff(c_506,plain,(
    ! [C_193,A_194,D_195,B_196] :
      ( m1_orders_2(C_193,A_194,D_195)
      | m1_orders_2(D_195,A_194,C_193)
      | D_195 = C_193
      | ~ m2_orders_2(D_195,A_194,B_196)
      | ~ m2_orders_2(C_193,A_194,B_196)
      | ~ m1_orders_1(B_196,k1_orders_1(u1_struct_0(A_194)))
      | ~ l1_orders_2(A_194)
      | ~ v5_orders_2(A_194)
      | ~ v4_orders_2(A_194)
      | ~ v3_orders_2(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_508,plain,(
    ! [C_193] :
      ( m1_orders_2(C_193,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_193)
      | C_193 = '#skF_4'
      | ~ m2_orders_2(C_193,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_506])).

tff(c_513,plain,(
    ! [C_193] :
      ( m1_orders_2(C_193,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_193)
      | C_193 = '#skF_4'
      | ~ m2_orders_2(C_193,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_508])).

tff(c_519,plain,(
    ! [C_197] :
      ( m1_orders_2(C_197,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_197)
      | C_197 = '#skF_4'
      | ~ m2_orders_2(C_197,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_513])).

tff(c_525,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_519])).

tff(c_530,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_525])).

tff(c_544,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_565,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_238])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_565])).

tff(c_572,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_30,plain,(
    ! [C_41,B_39,A_35] :
      ( r1_tarski(C_41,B_39)
      | ~ m1_orders_2(C_41,A_35,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_orders_2(A_35)
      | ~ v5_orders_2(A_35)
      | ~ v4_orders_2(A_35)
      | ~ v3_orders_2(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_591,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_572,c_30])).

tff(c_602,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_485,c_591])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_269,c_602])).

tff(c_605,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_610,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_238])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_610])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:26:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.45  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k7_subset_1 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.06/1.45  
% 3.06/1.45  %Foreground sorts:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Background operators:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Foreground operators:
% 3.06/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.06/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.06/1.45  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.45  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.06/1.45  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.06/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.45  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.06/1.45  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.06/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.45  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.06/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.06/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.06/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.45  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.06/1.45  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 3.06/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.06/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.06/1.45  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.45  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.06/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.45  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.06/1.45  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.06/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.45  
% 3.06/1.47  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.06/1.47  tff(f_195, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 3.06/1.47  tff(f_98, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.06/1.47  tff(f_117, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 3.06/1.47  tff(f_142, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 3.06/1.47  tff(f_76, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 3.06/1.47  tff(f_37, axiom, (![A, B]: ~(r2_xboole_0(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_xboole_1)).
% 3.06/1.47  tff(f_170, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 3.06/1.47  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.47  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_251, plain, (![A_137, B_138]: (r2_xboole_0(A_137, B_138) | B_138=A_137 | ~r1_tarski(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.47  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_42, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_50, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_48, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_46, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_44, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_171, plain, (![C_112, A_113, B_114]: (v6_orders_2(C_112, A_113) | ~m2_orders_2(C_112, A_113, B_114) | ~m1_orders_1(B_114, k1_orders_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.47  tff(c_173, plain, (v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_171])).
% 3.06/1.47  tff(c_176, plain, (v6_orders_2('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_173])).
% 3.06/1.47  tff(c_177, plain, (v6_orders_2('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_176])).
% 3.06/1.47  tff(c_185, plain, (![C_118, A_119, B_120]: (m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~m2_orders_2(C_118, A_119, B_120) | ~m1_orders_1(B_120, k1_orders_1(u1_struct_0(A_119))) | ~l1_orders_2(A_119) | ~v5_orders_2(A_119) | ~v4_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.47  tff(c_187, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_185])).
% 3.06/1.47  tff(c_190, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_187])).
% 3.06/1.47  tff(c_191, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_190])).
% 3.06/1.47  tff(c_67, plain, (![A_80, B_81]: (r2_xboole_0(A_80, B_81) | B_81=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.47  tff(c_60, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_62, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 3.06/1.47  tff(c_54, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_66, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54])).
% 3.06/1.47  tff(c_80, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_67, c_66])).
% 3.06/1.47  tff(c_94, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 3.06/1.47  tff(c_119, plain, (![C_96, B_97, A_98]: (r1_tarski(C_96, B_97) | ~m1_orders_2(C_96, A_98, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.06/1.47  tff(c_121, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_119])).
% 3.06/1.47  tff(c_124, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_121])).
% 3.06/1.47  tff(c_125, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_94, c_124])).
% 3.06/1.47  tff(c_38, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.06/1.47  tff(c_126, plain, (![C_99, A_100, B_101]: (m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~m2_orders_2(C_99, A_100, B_101) | ~m1_orders_1(B_101, k1_orders_1(u1_struct_0(A_100))) | ~l1_orders_2(A_100) | ~v5_orders_2(A_100) | ~v4_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.47  tff(c_130, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_126])).
% 3.06/1.47  tff(c_137, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_130])).
% 3.06/1.47  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_125, c_137])).
% 3.06/1.47  tff(c_140, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_80])).
% 3.06/1.47  tff(c_143, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_62])).
% 3.06/1.47  tff(c_193, plain, (![C_123, A_124, B_125]: (~m1_orders_2(C_123, A_124, B_125) | ~m1_orders_2(B_125, A_124, C_123) | k1_xboole_0=B_125 | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.06/1.47  tff(c_195, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_143, c_193])).
% 3.06/1.47  tff(c_198, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_191, c_143, c_195])).
% 3.06/1.47  tff(c_199, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_198])).
% 3.06/1.47  tff(c_22, plain, (![A_8, B_20]: (~m2_orders_2(k1_xboole_0, A_8, B_20) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_8))) | ~v6_orders_2(k1_xboole_0, A_8) | ~m1_orders_1(B_20, k1_orders_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.06/1.47  tff(c_216, plain, (![A_127, B_128]: (~m2_orders_2('#skF_4', A_127, B_128) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_127))) | ~v6_orders_2('#skF_4', A_127) | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_199, c_199, c_22])).
% 3.06/1.47  tff(c_218, plain, (![B_128]: (~m2_orders_2('#skF_4', '#skF_2', B_128) | ~v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_191, c_216])).
% 3.06/1.47  tff(c_221, plain, (![B_128]: (~m2_orders_2('#skF_4', '#skF_2', B_128) | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_177, c_218])).
% 3.06/1.47  tff(c_230, plain, (![B_132]: (~m2_orders_2('#skF_4', '#skF_2', B_132) | ~m1_orders_1(B_132, k1_orders_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_221])).
% 3.06/1.47  tff(c_233, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_230])).
% 3.06/1.47  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_233])).
% 3.06/1.47  tff(c_238, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 3.06/1.47  tff(c_247, plain, (![B_135, A_136]: (~r2_xboole_0(B_135, A_136) | ~r2_xboole_0(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.47  tff(c_250, plain, (~r2_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_238, c_247])).
% 3.06/1.47  tff(c_264, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_251, c_250])).
% 3.06/1.47  tff(c_269, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_264])).
% 3.06/1.47  tff(c_477, plain, (![C_178, A_179, B_180]: (m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~m2_orders_2(C_178, A_179, B_180) | ~m1_orders_1(B_180, k1_orders_1(u1_struct_0(A_179))) | ~l1_orders_2(A_179) | ~v5_orders_2(A_179) | ~v4_orders_2(A_179) | ~v3_orders_2(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.47  tff(c_479, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_477])).
% 3.06/1.47  tff(c_484, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_479])).
% 3.06/1.47  tff(c_485, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_484])).
% 3.06/1.47  tff(c_241, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_54])).
% 3.06/1.47  tff(c_506, plain, (![C_193, A_194, D_195, B_196]: (m1_orders_2(C_193, A_194, D_195) | m1_orders_2(D_195, A_194, C_193) | D_195=C_193 | ~m2_orders_2(D_195, A_194, B_196) | ~m2_orders_2(C_193, A_194, B_196) | ~m1_orders_1(B_196, k1_orders_1(u1_struct_0(A_194))) | ~l1_orders_2(A_194) | ~v5_orders_2(A_194) | ~v4_orders_2(A_194) | ~v3_orders_2(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.06/1.47  tff(c_508, plain, (![C_193]: (m1_orders_2(C_193, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_193) | C_193='#skF_4' | ~m2_orders_2(C_193, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_506])).
% 3.06/1.47  tff(c_513, plain, (![C_193]: (m1_orders_2(C_193, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_193) | C_193='#skF_4' | ~m2_orders_2(C_193, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_508])).
% 3.06/1.47  tff(c_519, plain, (![C_197]: (m1_orders_2(C_197, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_197) | C_197='#skF_4' | ~m2_orders_2(C_197, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_513])).
% 3.06/1.47  tff(c_525, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_519])).
% 3.06/1.47  tff(c_530, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_241, c_525])).
% 3.06/1.47  tff(c_544, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_530])).
% 3.06/1.47  tff(c_565, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_544, c_238])).
% 3.06/1.47  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_565])).
% 3.06/1.47  tff(c_572, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_530])).
% 3.06/1.47  tff(c_30, plain, (![C_41, B_39, A_35]: (r1_tarski(C_41, B_39) | ~m1_orders_2(C_41, A_35, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_orders_2(A_35) | ~v5_orders_2(A_35) | ~v4_orders_2(A_35) | ~v3_orders_2(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.06/1.47  tff(c_591, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_572, c_30])).
% 3.06/1.47  tff(c_602, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_485, c_591])).
% 3.06/1.47  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_269, c_602])).
% 3.06/1.47  tff(c_605, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_264])).
% 3.06/1.47  tff(c_610, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_238])).
% 3.06/1.47  tff(c_613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_610])).
% 3.06/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  Inference rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Ref     : 0
% 3.06/1.47  #Sup     : 98
% 3.06/1.47  #Fact    : 0
% 3.06/1.47  #Define  : 0
% 3.06/1.47  #Split   : 4
% 3.06/1.47  #Chain   : 0
% 3.06/1.47  #Close   : 0
% 3.06/1.47  
% 3.06/1.47  Ordering : KBO
% 3.06/1.47  
% 3.06/1.47  Simplification rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Subsume      : 39
% 3.06/1.47  #Demod        : 183
% 3.06/1.47  #Tautology    : 26
% 3.06/1.47  #SimpNegUnit  : 28
% 3.06/1.47  #BackRed      : 31
% 3.06/1.47  
% 3.06/1.47  #Partial instantiations: 0
% 3.06/1.47  #Strategies tried      : 1
% 3.06/1.47  
% 3.06/1.47  Timing (in seconds)
% 3.06/1.47  ----------------------
% 3.06/1.47  Preprocessing        : 0.33
% 3.06/1.47  Parsing              : 0.18
% 3.06/1.47  CNF conversion       : 0.03
% 3.06/1.47  Main loop            : 0.33
% 3.06/1.47  Inferencing          : 0.12
% 3.06/1.47  Reduction            : 0.10
% 3.06/1.47  Demodulation         : 0.07
% 3.06/1.47  BG Simplification    : 0.02
% 3.06/1.47  Subsumption          : 0.07
% 3.06/1.47  Abstraction          : 0.01
% 3.06/1.47  MUC search           : 0.00
% 3.06/1.47  Cooper               : 0.00
% 3.06/1.47  Total                : 0.71
% 3.06/1.47  Index Insertion      : 0.00
% 3.06/1.47  Index Deletion       : 0.00
% 3.06/1.47  Index Matching       : 0.00
% 3.06/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
