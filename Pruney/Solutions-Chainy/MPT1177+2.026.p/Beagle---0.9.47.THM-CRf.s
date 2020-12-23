%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:58 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 381 expanded)
%              Number of leaves         :   36 ( 153 expanded)
%              Depth                    :   14
%              Number of atoms          :  321 (1589 expanded)
%              Number of equality atoms :   33 (  78 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_208,negated_conjecture,(
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

tff(f_88,axiom,(
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

tff(f_107,axiom,(
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

tff(f_132,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_155,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(f_183,axiom,(
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

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_52,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_50,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_48,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_44,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1197,plain,(
    ! [C_187,A_188,B_189] :
      ( m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m2_orders_2(C_187,A_188,B_189)
      | ~ m1_orders_1(B_189,k1_orders_1(u1_struct_0(A_188)))
      | ~ l1_orders_2(A_188)
      | ~ v5_orders_2(A_188)
      | ~ v4_orders_2(A_188)
      | ~ v3_orders_2(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1199,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1197])).

tff(c_1202,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_1199])).

tff(c_1203,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1202])).

tff(c_190,plain,(
    ! [A_98,B_99] :
      ( r2_xboole_0(A_98,B_99)
      | B_99 = A_98
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_92,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_201,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_190,c_92])).

tff(c_207,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_139,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_62])).

tff(c_606,plain,(
    ! [C_132,B_133,A_134] :
      ( r1_tarski(C_132,B_133)
      | ~ m1_orders_2(C_132,A_134,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_608,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_139,c_606])).

tff(c_611,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_608])).

tff(c_612,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_207,c_611])).

tff(c_745,plain,(
    ! [C_146,A_147,B_148] :
      ( m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ m2_orders_2(C_146,A_147,B_148)
      | ~ m1_orders_1(B_148,k1_orders_1(u1_struct_0(A_147)))
      | ~ l1_orders_2(A_147)
      | ~ v5_orders_2(A_147)
      | ~ v4_orders_2(A_147)
      | ~ v3_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_749,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_745])).

tff(c_756,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_749])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_612,c_756])).

tff(c_759,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_761,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_139])).

tff(c_1668,plain,(
    ! [C_221,A_222,B_223] :
      ( ~ m1_orders_2(C_221,A_222,B_223)
      | ~ m1_orders_2(B_223,A_222,C_221)
      | k1_xboole_0 = B_223
      | ~ m1_subset_1(C_221,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_orders_2(A_222)
      | ~ v5_orders_2(A_222)
      | ~ v4_orders_2(A_222)
      | ~ v3_orders_2(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1670,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_761,c_1668])).

tff(c_1673,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1203,c_761,c_1670])).

tff(c_1674,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1673])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_77,plain,(
    ! [B_83] : k4_xboole_0(B_83,B_83) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_22,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [B_83] : r1_tarski(k1_xboole_0,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_22])).

tff(c_1704,plain,(
    ! [B_224] : r1_tarski('#skF_4',B_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_82])).

tff(c_770,plain,(
    ! [B_149,A_150] :
      ( B_149 = A_150
      | ~ r1_tarski(B_149,A_150)
      | ~ r1_tarski(A_150,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_781,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,k4_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_22,c_770])).

tff(c_1719,plain,(
    ! [B_11] : k4_xboole_0('#skF_4',B_11) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1704,c_781])).

tff(c_75,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_1695,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_75])).

tff(c_145,plain,(
    ! [A_90,C_91,B_92] :
      ( r1_xboole_0(A_90,C_91)
      | ~ r1_tarski(A_90,k4_xboole_0(B_92,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_173,plain,(
    ! [B_92,C_91,B_11] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_92,C_91),B_11),C_91) ),
    inference(resolution,[status(thm)],[c_22,c_145])).

tff(c_1412,plain,(
    ! [C_207,D_208,A_209,B_210] :
      ( ~ r1_xboole_0(C_207,D_208)
      | ~ m2_orders_2(D_208,A_209,B_210)
      | ~ m2_orders_2(C_207,A_209,B_210)
      | ~ m1_orders_1(B_210,k1_orders_1(u1_struct_0(A_209)))
      | ~ l1_orders_2(A_209)
      | ~ v5_orders_2(A_209)
      | ~ v4_orders_2(A_209)
      | ~ v3_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4036,plain,(
    ! [A_330,B_328,C_327,B_329,B_326] :
      ( ~ m2_orders_2(C_327,A_330,B_326)
      | ~ m2_orders_2(k4_xboole_0(k4_xboole_0(B_328,C_327),B_329),A_330,B_326)
      | ~ m1_orders_1(B_326,k1_orders_1(u1_struct_0(A_330)))
      | ~ l1_orders_2(A_330)
      | ~ v5_orders_2(A_330)
      | ~ v4_orders_2(A_330)
      | ~ v3_orders_2(A_330)
      | v2_struct_0(A_330) ) ),
    inference(resolution,[status(thm)],[c_173,c_1412])).

tff(c_4063,plain,(
    ! [A_10,A_330,B_326,B_329] :
      ( ~ m2_orders_2(A_10,A_330,B_326)
      | ~ m2_orders_2(k4_xboole_0('#skF_4',B_329),A_330,B_326)
      | ~ m1_orders_1(B_326,k1_orders_1(u1_struct_0(A_330)))
      | ~ l1_orders_2(A_330)
      | ~ v5_orders_2(A_330)
      | ~ v4_orders_2(A_330)
      | ~ v3_orders_2(A_330)
      | v2_struct_0(A_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1695,c_4036])).

tff(c_9530,plain,(
    ! [A_440,A_441,B_442] :
      ( ~ m2_orders_2(A_440,A_441,B_442)
      | ~ m2_orders_2('#skF_4',A_441,B_442)
      | ~ m1_orders_1(B_442,k1_orders_1(u1_struct_0(A_441)))
      | ~ l1_orders_2(A_441)
      | ~ v5_orders_2(A_441)
      | ~ v4_orders_2(A_441)
      | ~ v3_orders_2(A_441)
      | v2_struct_0(A_441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1719,c_4063])).

tff(c_9532,plain,
    ( ~ m2_orders_2('#skF_4','#skF_1','#skF_2')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_9530])).

tff(c_9535,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_40,c_9532])).

tff(c_9537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9535])).

tff(c_9539,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9543,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_9539,c_6])).

tff(c_9845,plain,(
    ! [B_472,A_473] :
      ( B_472 = A_473
      | ~ r1_tarski(B_472,A_473)
      | ~ r1_tarski(A_473,B_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9863,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_9543,c_9845])).

tff(c_9870,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_9863])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_10148,plain,(
    ! [C_498,A_499,B_500] :
      ( m1_subset_1(C_498,k1_zfmisc_1(u1_struct_0(A_499)))
      | ~ m2_orders_2(C_498,A_499,B_500)
      | ~ m1_orders_1(B_500,k1_orders_1(u1_struct_0(A_499)))
      | ~ l1_orders_2(A_499)
      | ~ v5_orders_2(A_499)
      | ~ v4_orders_2(A_499)
      | ~ v3_orders_2(A_499)
      | v2_struct_0(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10150,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_10148])).

tff(c_10155,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_10150])).

tff(c_10156,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_10155])).

tff(c_76,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_9538,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_10648,plain,(
    ! [C_532,A_533,D_534,B_535] :
      ( m1_orders_2(C_532,A_533,D_534)
      | m1_orders_2(D_534,A_533,C_532)
      | D_534 = C_532
      | ~ m2_orders_2(D_534,A_533,B_535)
      | ~ m2_orders_2(C_532,A_533,B_535)
      | ~ m1_orders_1(B_535,k1_orders_1(u1_struct_0(A_533)))
      | ~ l1_orders_2(A_533)
      | ~ v5_orders_2(A_533)
      | ~ v4_orders_2(A_533)
      | ~ v3_orders_2(A_533)
      | v2_struct_0(A_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_10652,plain,(
    ! [C_532] :
      ( m1_orders_2(C_532,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_532)
      | C_532 = '#skF_4'
      | ~ m2_orders_2(C_532,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_10648])).

tff(c_10659,plain,(
    ! [C_532] :
      ( m1_orders_2(C_532,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_532)
      | C_532 = '#skF_4'
      | ~ m2_orders_2(C_532,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_10652])).

tff(c_10892,plain,(
    ! [C_544] :
      ( m1_orders_2(C_544,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_544)
      | C_544 = '#skF_4'
      | ~ m2_orders_2(C_544,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_10659])).

tff(c_10895,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_10892])).

tff(c_10901,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_9538,c_10895])).

tff(c_10904,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10901])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9878,plain,(
    k4_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_9870])).

tff(c_10907,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10904,c_9878])).

tff(c_10918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10907])).

tff(c_10919,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_10901])).

tff(c_30,plain,(
    ! [C_26,B_24,A_20] :
      ( r1_tarski(C_26,B_24)
      | ~ m1_orders_2(C_26,A_20,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20)
      | ~ v4_orders_2(A_20)
      | ~ v3_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10926,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10919,c_30])).

tff(c_10937,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_10156,c_10926])).

tff(c_10939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9870,c_10937])).

tff(c_10940,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9863])).

tff(c_10945,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10940,c_9539])).

tff(c_10950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_10945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:01:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.01/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.56  
% 7.01/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.56  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.01/2.56  
% 7.01/2.56  %Foreground sorts:
% 7.01/2.56  
% 7.01/2.56  
% 7.01/2.56  %Background operators:
% 7.01/2.56  
% 7.01/2.56  
% 7.01/2.56  %Foreground operators:
% 7.01/2.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.01/2.56  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.01/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.01/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.01/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.01/2.56  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 7.01/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.01/2.56  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 7.01/2.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.01/2.56  tff('#skF_2', type, '#skF_2': $i).
% 7.01/2.56  tff('#skF_3', type, '#skF_3': $i).
% 7.01/2.56  tff('#skF_1', type, '#skF_1': $i).
% 7.01/2.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.01/2.56  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.01/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.01/2.56  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 7.01/2.56  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.01/2.56  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 7.01/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.01/2.56  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 7.01/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.01/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.01/2.56  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 7.01/2.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.01/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.01/2.56  
% 7.01/2.58  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 7.01/2.58  tff(f_208, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 7.01/2.58  tff(f_88, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 7.01/2.58  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 7.01/2.58  tff(f_132, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 7.01/2.58  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.01/2.58  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.01/2.58  tff(f_50, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.01/2.58  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.01/2.58  tff(f_155, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 7.01/2.58  tff(f_183, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 7.01/2.58  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.01/2.58  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_1197, plain, (![C_187, A_188, B_189]: (m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~m2_orders_2(C_187, A_188, B_189) | ~m1_orders_1(B_189, k1_orders_1(u1_struct_0(A_188))) | ~l1_orders_2(A_188) | ~v5_orders_2(A_188) | ~v4_orders_2(A_188) | ~v3_orders_2(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.01/2.58  tff(c_1199, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1197])).
% 7.01/2.58  tff(c_1202, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_1199])).
% 7.01/2.58  tff(c_1203, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_1202])).
% 7.01/2.58  tff(c_190, plain, (![A_98, B_99]: (r2_xboole_0(A_98, B_99) | B_99=A_98 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.01/2.58  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_92, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 7.01/2.58  tff(c_201, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_190, c_92])).
% 7.01/2.58  tff(c_207, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_201])).
% 7.01/2.58  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_139, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_62])).
% 7.01/2.58  tff(c_606, plain, (![C_132, B_133, A_134]: (r1_tarski(C_132, B_133) | ~m1_orders_2(C_132, A_134, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.01/2.58  tff(c_608, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_139, c_606])).
% 7.01/2.58  tff(c_611, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_608])).
% 7.01/2.58  tff(c_612, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_207, c_611])).
% 7.01/2.58  tff(c_745, plain, (![C_146, A_147, B_148]: (m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~m2_orders_2(C_146, A_147, B_148) | ~m1_orders_1(B_148, k1_orders_1(u1_struct_0(A_147))) | ~l1_orders_2(A_147) | ~v5_orders_2(A_147) | ~v4_orders_2(A_147) | ~v3_orders_2(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.01/2.58  tff(c_749, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_745])).
% 7.01/2.58  tff(c_756, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_749])).
% 7.01/2.58  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_612, c_756])).
% 7.01/2.58  tff(c_759, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_201])).
% 7.01/2.58  tff(c_761, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_759, c_139])).
% 7.01/2.58  tff(c_1668, plain, (![C_221, A_222, B_223]: (~m1_orders_2(C_221, A_222, B_223) | ~m1_orders_2(B_223, A_222, C_221) | k1_xboole_0=B_223 | ~m1_subset_1(C_221, k1_zfmisc_1(u1_struct_0(A_222))) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_orders_2(A_222) | ~v5_orders_2(A_222) | ~v4_orders_2(A_222) | ~v3_orders_2(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.01/2.58  tff(c_1670, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_761, c_1668])).
% 7.01/2.58  tff(c_1673, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1203, c_761, c_1670])).
% 7.01/2.58  tff(c_1674, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_1673])).
% 7.01/2.58  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.01/2.58  tff(c_68, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.01/2.58  tff(c_77, plain, (![B_83]: (k4_xboole_0(B_83, B_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_68])).
% 7.01/2.58  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.01/2.58  tff(c_82, plain, (![B_83]: (r1_tarski(k1_xboole_0, B_83))), inference(superposition, [status(thm), theory('equality')], [c_77, c_22])).
% 7.01/2.58  tff(c_1704, plain, (![B_224]: (r1_tarski('#skF_4', B_224))), inference(demodulation, [status(thm), theory('equality')], [c_1674, c_82])).
% 7.01/2.58  tff(c_770, plain, (![B_149, A_150]: (B_149=A_150 | ~r1_tarski(B_149, A_150) | ~r1_tarski(A_150, B_149))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.01/2.58  tff(c_781, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_22, c_770])).
% 7.01/2.58  tff(c_1719, plain, (![B_11]: (k4_xboole_0('#skF_4', B_11)='#skF_4')), inference(resolution, [status(thm)], [c_1704, c_781])).
% 7.01/2.58  tff(c_75, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_68])).
% 7.01/2.58  tff(c_1695, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1674, c_75])).
% 7.01/2.58  tff(c_145, plain, (![A_90, C_91, B_92]: (r1_xboole_0(A_90, C_91) | ~r1_tarski(A_90, k4_xboole_0(B_92, C_91)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.01/2.58  tff(c_173, plain, (![B_92, C_91, B_11]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_92, C_91), B_11), C_91))), inference(resolution, [status(thm)], [c_22, c_145])).
% 7.01/2.58  tff(c_1412, plain, (![C_207, D_208, A_209, B_210]: (~r1_xboole_0(C_207, D_208) | ~m2_orders_2(D_208, A_209, B_210) | ~m2_orders_2(C_207, A_209, B_210) | ~m1_orders_1(B_210, k1_orders_1(u1_struct_0(A_209))) | ~l1_orders_2(A_209) | ~v5_orders_2(A_209) | ~v4_orders_2(A_209) | ~v3_orders_2(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.01/2.58  tff(c_4036, plain, (![A_330, B_328, C_327, B_329, B_326]: (~m2_orders_2(C_327, A_330, B_326) | ~m2_orders_2(k4_xboole_0(k4_xboole_0(B_328, C_327), B_329), A_330, B_326) | ~m1_orders_1(B_326, k1_orders_1(u1_struct_0(A_330))) | ~l1_orders_2(A_330) | ~v5_orders_2(A_330) | ~v4_orders_2(A_330) | ~v3_orders_2(A_330) | v2_struct_0(A_330))), inference(resolution, [status(thm)], [c_173, c_1412])).
% 7.01/2.58  tff(c_4063, plain, (![A_10, A_330, B_326, B_329]: (~m2_orders_2(A_10, A_330, B_326) | ~m2_orders_2(k4_xboole_0('#skF_4', B_329), A_330, B_326) | ~m1_orders_1(B_326, k1_orders_1(u1_struct_0(A_330))) | ~l1_orders_2(A_330) | ~v5_orders_2(A_330) | ~v4_orders_2(A_330) | ~v3_orders_2(A_330) | v2_struct_0(A_330))), inference(superposition, [status(thm), theory('equality')], [c_1695, c_4036])).
% 7.01/2.58  tff(c_9530, plain, (![A_440, A_441, B_442]: (~m2_orders_2(A_440, A_441, B_442) | ~m2_orders_2('#skF_4', A_441, B_442) | ~m1_orders_1(B_442, k1_orders_1(u1_struct_0(A_441))) | ~l1_orders_2(A_441) | ~v5_orders_2(A_441) | ~v4_orders_2(A_441) | ~v3_orders_2(A_441) | v2_struct_0(A_441))), inference(demodulation, [status(thm), theory('equality')], [c_1719, c_4063])).
% 7.01/2.58  tff(c_9532, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_9530])).
% 7.01/2.58  tff(c_9535, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_40, c_9532])).
% 7.01/2.58  tff(c_9537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_9535])).
% 7.01/2.58  tff(c_9539, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 7.01/2.58  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.01/2.58  tff(c_9543, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_9539, c_6])).
% 7.01/2.58  tff(c_9845, plain, (![B_472, A_473]: (B_472=A_473 | ~r1_tarski(B_472, A_473) | ~r1_tarski(A_473, B_472))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.01/2.58  tff(c_9863, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_9543, c_9845])).
% 7.01/2.58  tff(c_9870, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_9863])).
% 7.01/2.58  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.01/2.58  tff(c_10148, plain, (![C_498, A_499, B_500]: (m1_subset_1(C_498, k1_zfmisc_1(u1_struct_0(A_499))) | ~m2_orders_2(C_498, A_499, B_500) | ~m1_orders_1(B_500, k1_orders_1(u1_struct_0(A_499))) | ~l1_orders_2(A_499) | ~v5_orders_2(A_499) | ~v4_orders_2(A_499) | ~v3_orders_2(A_499) | v2_struct_0(A_499))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.01/2.58  tff(c_10150, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_10148])).
% 7.01/2.58  tff(c_10155, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_10150])).
% 7.01/2.58  tff(c_10156, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_10155])).
% 7.01/2.58  tff(c_76, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_68])).
% 7.01/2.58  tff(c_9538, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 7.01/2.58  tff(c_10648, plain, (![C_532, A_533, D_534, B_535]: (m1_orders_2(C_532, A_533, D_534) | m1_orders_2(D_534, A_533, C_532) | D_534=C_532 | ~m2_orders_2(D_534, A_533, B_535) | ~m2_orders_2(C_532, A_533, B_535) | ~m1_orders_1(B_535, k1_orders_1(u1_struct_0(A_533))) | ~l1_orders_2(A_533) | ~v5_orders_2(A_533) | ~v4_orders_2(A_533) | ~v3_orders_2(A_533) | v2_struct_0(A_533))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.01/2.58  tff(c_10652, plain, (![C_532]: (m1_orders_2(C_532, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_532) | C_532='#skF_4' | ~m2_orders_2(C_532, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_10648])).
% 7.01/2.58  tff(c_10659, plain, (![C_532]: (m1_orders_2(C_532, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_532) | C_532='#skF_4' | ~m2_orders_2(C_532, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_10652])).
% 7.01/2.58  tff(c_10892, plain, (![C_544]: (m1_orders_2(C_544, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_544) | C_544='#skF_4' | ~m2_orders_2(C_544, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_10659])).
% 7.01/2.58  tff(c_10895, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_10892])).
% 7.01/2.58  tff(c_10901, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_9538, c_10895])).
% 7.01/2.58  tff(c_10904, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_10901])).
% 7.01/2.58  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.01/2.58  tff(c_9878, plain, (k4_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_9870])).
% 7.01/2.58  tff(c_10907, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10904, c_9878])).
% 7.01/2.58  tff(c_10918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_10907])).
% 7.01/2.58  tff(c_10919, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_10901])).
% 7.01/2.58  tff(c_30, plain, (![C_26, B_24, A_20]: (r1_tarski(C_26, B_24) | ~m1_orders_2(C_26, A_20, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.01/2.58  tff(c_10926, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10919, c_30])).
% 7.01/2.58  tff(c_10937, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_10156, c_10926])).
% 7.01/2.58  tff(c_10939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_9870, c_10937])).
% 7.01/2.58  tff(c_10940, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_9863])).
% 7.01/2.58  tff(c_10945, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10940, c_9539])).
% 7.01/2.58  tff(c_10950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_10945])).
% 7.01/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.58  
% 7.01/2.58  Inference rules
% 7.01/2.58  ----------------------
% 7.01/2.58  #Ref     : 0
% 7.01/2.58  #Sup     : 2678
% 7.01/2.58  #Fact    : 0
% 7.01/2.58  #Define  : 0
% 7.01/2.58  #Split   : 4
% 7.01/2.58  #Chain   : 0
% 7.01/2.58  #Close   : 0
% 7.01/2.58  
% 7.01/2.58  Ordering : KBO
% 7.01/2.58  
% 7.01/2.58  Simplification rules
% 7.01/2.58  ----------------------
% 7.01/2.58  #Subsume      : 879
% 7.01/2.58  #Demod        : 2662
% 7.01/2.58  #Tautology    : 1269
% 7.01/2.58  #SimpNegUnit  : 27
% 7.01/2.58  #BackRed      : 42
% 7.01/2.58  
% 7.01/2.58  #Partial instantiations: 0
% 7.01/2.58  #Strategies tried      : 1
% 7.01/2.58  
% 7.01/2.58  Timing (in seconds)
% 7.01/2.58  ----------------------
% 7.01/2.58  Preprocessing        : 0.34
% 7.01/2.59  Parsing              : 0.19
% 7.01/2.59  CNF conversion       : 0.03
% 7.01/2.59  Main loop            : 1.46
% 7.25/2.59  Inferencing          : 0.47
% 7.25/2.59  Reduction            : 0.55
% 7.25/2.59  Demodulation         : 0.43
% 7.25/2.59  BG Simplification    : 0.05
% 7.25/2.59  Subsumption          : 0.31
% 7.25/2.59  Abstraction          : 0.07
% 7.25/2.59  MUC search           : 0.00
% 7.25/2.59  Cooper               : 0.00
% 7.25/2.59  Total                : 1.85
% 7.25/2.59  Index Insertion      : 0.00
% 7.25/2.59  Index Deletion       : 0.00
% 7.25/2.59  Index Matching       : 0.00
% 7.25/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
