%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:24 EST 2020

% Result     : Theorem 13.94s
% Output     : CNFRefutation 14.17s
% Verified   : 
% Statistics : Number of formulae       :  126 (1114 expanded)
%              Number of leaves         :   41 ( 430 expanded)
%              Depth                    :   21
%              Number of atoms          :  338 (3449 expanded)
%              Number of equality atoms :   45 ( 635 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_zfmisc_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    ! [A_44] :
      ( l1_struct_0(A_44)
      | ~ l1_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_103,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_115,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_orders_2(A_68) ) ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_119,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_115])).

tff(c_66,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_62,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_481,plain,(
    ! [A_141,B_142] :
      ( k1_orders_2(A_141,B_142) = a_2_0_orders_2(A_141,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_496,plain,(
    ! [B_142] :
      ( k1_orders_2('#skF_4',B_142) = a_2_0_orders_2('#skF_4',B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_481])).

tff(c_505,plain,(
    ! [B_142] :
      ( k1_orders_2('#skF_4',B_142) = a_2_0_orders_2('#skF_4',B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_496])).

tff(c_508,plain,(
    ! [B_143] :
      ( k1_orders_2('#skF_4',B_143) = a_2_0_orders_2('#skF_4',B_143)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_505])).

tff(c_533,plain,(
    ! [A_144] :
      ( k1_orders_2('#skF_4',A_144) = a_2_0_orders_2('#skF_4',A_144)
      | ~ r1_tarski(A_144,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_22,c_508])).

tff(c_549,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_533])).

tff(c_58,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_567,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_58])).

tff(c_26,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_1'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_191,plain,(
    ! [C_89,A_90,B_91] :
      ( r2_hidden(C_89,A_90)
      | ~ r2_hidden(C_89,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_200,plain,(
    ! [A_99,A_100] :
      ( r2_hidden('#skF_1'(A_99),A_100)
      | ~ m1_subset_1(A_99,k1_zfmisc_1(A_100))
      | k1_xboole_0 = A_99 ) ),
    inference(resolution,[status(thm)],[c_26,c_191])).

tff(c_16,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3327,plain,(
    ! [A_283,A_284,A_285] :
      ( r2_hidden('#skF_1'(A_283),A_284)
      | ~ m1_subset_1(A_285,k1_zfmisc_1(A_284))
      | ~ m1_subset_1(A_283,k1_zfmisc_1(A_285))
      | k1_xboole_0 = A_283 ) ),
    inference(resolution,[status(thm)],[c_200,c_16])).

tff(c_3712,plain,(
    ! [A_298,B_299,A_300] :
      ( r2_hidden('#skF_1'(A_298),B_299)
      | ~ m1_subset_1(A_298,k1_zfmisc_1(A_300))
      | k1_xboole_0 = A_298
      | ~ r1_tarski(A_300,B_299) ) ),
    inference(resolution,[status(thm)],[c_22,c_3327])).

tff(c_3772,plain,(
    ! [A_301,B_302,B_303] :
      ( r2_hidden('#skF_1'(A_301),B_302)
      | k1_xboole_0 = A_301
      | ~ r1_tarski(B_303,B_302)
      | ~ r1_tarski(A_301,B_303) ) ),
    inference(resolution,[status(thm)],[c_22,c_3712])).

tff(c_3812,plain,(
    ! [A_301,B_2] :
      ( r2_hidden('#skF_1'(A_301),B_2)
      | k1_xboole_0 = A_301
      | ~ r1_tarski(A_301,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_3772])).

tff(c_623,plain,(
    ! [A_152,B_153] :
      ( m1_subset_1(k1_orders_2(A_152,B_153),k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_636,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_623])).

tff(c_648,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_119,c_119,c_636])).

tff(c_649,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_648])).

tff(c_798,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_649])).

tff(c_801,plain,(
    ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_798])).

tff(c_805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_801])).

tff(c_807,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_649])).

tff(c_761,plain,(
    ! [A_156,B_157,C_158] :
      ( '#skF_2'(A_156,B_157,C_158) = A_156
      | ~ r2_hidden(A_156,a_2_0_orders_2(B_157,C_158))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(B_157)))
      | ~ l1_orders_2(B_157)
      | ~ v5_orders_2(B_157)
      | ~ v4_orders_2(B_157)
      | ~ v3_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3813,plain,(
    ! [B_304,C_305] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_304,C_305)),B_304,C_305) = '#skF_1'(a_2_0_orders_2(B_304,C_305))
      | ~ m1_subset_1(C_305,k1_zfmisc_1(u1_struct_0(B_304)))
      | ~ l1_orders_2(B_304)
      | ~ v5_orders_2(B_304)
      | ~ v4_orders_2(B_304)
      | ~ v3_orders_2(B_304)
      | v2_struct_0(B_304)
      | a_2_0_orders_2(B_304,C_305) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_761])).

tff(c_3838,plain,(
    ! [C_305] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_305)),'#skF_4',C_305) = '#skF_1'(a_2_0_orders_2('#skF_4',C_305))
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_305) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_3813])).

tff(c_3851,plain,(
    ! [C_305] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_305)),'#skF_4',C_305) = '#skF_1'(a_2_0_orders_2('#skF_4',C_305))
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_305) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_3838])).

tff(c_3997,plain,(
    ! [C_312] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_312)),'#skF_4',C_312) = '#skF_1'(a_2_0_orders_2('#skF_4',C_312))
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_0_orders_2('#skF_4',C_312) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3851])).

tff(c_4015,plain,
    ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_807,c_3997])).

tff(c_4042,plain,(
    '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_567,c_4015])).

tff(c_1345,plain,(
    ! [B_202,E_203,A_204,C_205] :
      ( r2_orders_2(B_202,E_203,'#skF_2'(A_204,B_202,C_205))
      | ~ r2_hidden(E_203,C_205)
      | ~ m1_subset_1(E_203,u1_struct_0(B_202))
      | ~ r2_hidden(A_204,a_2_0_orders_2(B_202,C_205))
      | ~ m1_subset_1(C_205,k1_zfmisc_1(u1_struct_0(B_202)))
      | ~ l1_orders_2(B_202)
      | ~ v5_orders_2(B_202)
      | ~ v4_orders_2(B_202)
      | ~ v3_orders_2(B_202)
      | v2_struct_0(B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1365,plain,(
    ! [B_202,E_203,A_204,A_12] :
      ( r2_orders_2(B_202,E_203,'#skF_2'(A_204,B_202,A_12))
      | ~ r2_hidden(E_203,A_12)
      | ~ m1_subset_1(E_203,u1_struct_0(B_202))
      | ~ r2_hidden(A_204,a_2_0_orders_2(B_202,A_12))
      | ~ l1_orders_2(B_202)
      | ~ v5_orders_2(B_202)
      | ~ v4_orders_2(B_202)
      | ~ v3_orders_2(B_202)
      | v2_struct_0(B_202)
      | ~ r1_tarski(A_12,u1_struct_0(B_202)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1345])).

tff(c_5031,plain,(
    ! [E_203] :
      ( r2_orders_2('#skF_4',E_203,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_203,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_203,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(k2_struct_0('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4042,c_1365])).

tff(c_5041,plain,(
    ! [E_203] :
      ( r2_orders_2('#skF_4',E_203,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_203,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_203,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_119,c_66,c_64,c_62,c_60,c_119,c_5031])).

tff(c_5042,plain,(
    ! [E_203] :
      ( r2_orders_2('#skF_4',E_203,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_203,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_203,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5041])).

tff(c_7216,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_5042])).

tff(c_7219,plain,
    ( a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
    | ~ r1_tarski(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_3812,c_7216])).

tff(c_7234,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7219])).

tff(c_7236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_567,c_7234])).

tff(c_7238,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_5042])).

tff(c_806,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_649])).

tff(c_24,plain,(
    ! [A_14,C_16,B_15] :
      ( m1_subset_1(A_14,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_910,plain,(
    ! [A_166] :
      ( m1_subset_1(A_166,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_166,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_806,c_24])).

tff(c_918,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_910])).

tff(c_922,plain,(
    m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_567,c_918])).

tff(c_18,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_528,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_508])).

tff(c_639,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_623])).

tff(c_651,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_18,c_119,c_639])).

tff(c_652,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_651])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_63,B_64] : ~ r2_hidden(A_63,k2_zfmisc_1(A_63,B_64)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_101,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_95])).

tff(c_1040,plain,(
    ! [D_172,B_173,C_174] :
      ( r2_hidden('#skF_3'(D_172,B_173,C_174,D_172),C_174)
      | r2_hidden(D_172,a_2_0_orders_2(B_173,C_174))
      | ~ m1_subset_1(D_172,u1_struct_0(B_173))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(B_173)))
      | ~ l1_orders_2(B_173)
      | ~ v5_orders_2(B_173)
      | ~ v4_orders_2(B_173)
      | ~ v3_orders_2(B_173)
      | v2_struct_0(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1053,plain,(
    ! [D_172,C_174] :
      ( r2_hidden('#skF_3'(D_172,'#skF_4',C_174,D_172),C_174)
      | r2_hidden(D_172,a_2_0_orders_2('#skF_4',C_174))
      | ~ m1_subset_1(D_172,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1040])).

tff(c_1062,plain,(
    ! [D_172,C_174] :
      ( r2_hidden('#skF_3'(D_172,'#skF_4',C_174,D_172),C_174)
      | r2_hidden(D_172,a_2_0_orders_2('#skF_4',C_174))
      | ~ m1_subset_1(D_172,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_119,c_1053])).

tff(c_1155,plain,(
    ! [D_181,C_182] :
      ( r2_hidden('#skF_3'(D_181,'#skF_4',C_182,D_181),C_182)
      | r2_hidden(D_181,a_2_0_orders_2('#skF_4',C_182))
      | ~ m1_subset_1(D_181,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1062])).

tff(c_1179,plain,(
    ! [D_181] :
      ( r2_hidden('#skF_3'(D_181,'#skF_4',k1_xboole_0,D_181),k1_xboole_0)
      | r2_hidden(D_181,a_2_0_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_181,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_1155])).

tff(c_1192,plain,(
    ! [D_183] :
      ( r2_hidden(D_183,a_2_0_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_183,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1179])).

tff(c_1309,plain,(
    ! [D_199,A_200] :
      ( r2_hidden(D_199,A_200)
      | ~ m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(A_200))
      | ~ m1_subset_1(D_199,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1192,c_16])).

tff(c_1320,plain,(
    ! [D_201] :
      ( r2_hidden(D_201,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_201,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_652,c_1309])).

tff(c_1597,plain,(
    ! [D_224,A_225] :
      ( r2_hidden(D_224,A_225)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(A_225))
      | ~ m1_subset_1(D_224,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1320,c_16])).

tff(c_1608,plain,(
    ! [D_226,B_227] :
      ( r2_hidden(D_226,B_227)
      | ~ m1_subset_1(D_226,k2_struct_0('#skF_4'))
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_227) ) ),
    inference(resolution,[status(thm)],[c_22,c_1597])).

tff(c_1852,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),B_235)
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_235) ) ),
    inference(resolution,[status(thm)],[c_922,c_1608])).

tff(c_9318,plain,(
    ! [A_503,B_504] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),A_503)
      | ~ m1_subset_1(B_504,k1_zfmisc_1(A_503))
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_504) ) ),
    inference(resolution,[status(thm)],[c_1852,c_16])).

tff(c_9357,plain,
    ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_807,c_9318])).

tff(c_9391,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9357])).

tff(c_4171,plain,(
    ! [B_319,E_320,A_321,A_322] :
      ( r2_orders_2(B_319,E_320,'#skF_2'(A_321,B_319,A_322))
      | ~ r2_hidden(E_320,A_322)
      | ~ m1_subset_1(E_320,u1_struct_0(B_319))
      | ~ r2_hidden(A_321,a_2_0_orders_2(B_319,A_322))
      | ~ l1_orders_2(B_319)
      | ~ v5_orders_2(B_319)
      | ~ v4_orders_2(B_319)
      | ~ v3_orders_2(B_319)
      | v2_struct_0(B_319)
      | ~ r1_tarski(A_322,u1_struct_0(B_319)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1345])).

tff(c_36,plain,(
    ! [A_32,C_38] :
      ( ~ r2_orders_2(A_32,C_38,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_11346,plain,(
    ! [A_587,B_588,A_589] :
      ( ~ r2_hidden('#skF_2'(A_587,B_588,A_589),A_589)
      | ~ m1_subset_1('#skF_2'(A_587,B_588,A_589),u1_struct_0(B_588))
      | ~ r2_hidden(A_587,a_2_0_orders_2(B_588,A_589))
      | ~ l1_orders_2(B_588)
      | ~ v5_orders_2(B_588)
      | ~ v4_orders_2(B_588)
      | ~ v3_orders_2(B_588)
      | v2_struct_0(B_588)
      | ~ r1_tarski(A_589,u1_struct_0(B_588)) ) ),
    inference(resolution,[status(thm)],[c_4171,c_36])).

tff(c_11356,plain,
    ( ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4042,c_11346])).

tff(c_11379,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_119,c_66,c_64,c_62,c_60,c_7238,c_922,c_119,c_4042,c_9391,c_11356])).

tff(c_11381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_11379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:51:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.94/5.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.94/5.85  
% 13.94/5.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.94/5.86  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_zfmisc_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 13.94/5.86  
% 13.94/5.86  %Foreground sorts:
% 13.94/5.86  
% 13.94/5.86  
% 13.94/5.86  %Background operators:
% 13.94/5.86  
% 13.94/5.86  
% 13.94/5.86  %Foreground operators:
% 13.94/5.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.94/5.86  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 13.94/5.86  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 13.94/5.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.94/5.86  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 13.94/5.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.94/5.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.94/5.86  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 13.94/5.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.94/5.86  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 13.94/5.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.94/5.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.94/5.86  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 13.94/5.86  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 13.94/5.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.94/5.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.94/5.86  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 13.94/5.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.94/5.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.94/5.86  tff('#skF_4', type, '#skF_4': $i).
% 13.94/5.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.94/5.86  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 13.94/5.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 13.94/5.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.94/5.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 13.94/5.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.94/5.86  
% 14.17/5.89  tff(f_170, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 14.17/5.89  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.17/5.89  tff(f_129, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 14.17/5.89  tff(f_79, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 14.17/5.89  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.17/5.89  tff(f_110, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 14.17/5.89  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 14.17/5.89  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 14.17/5.89  tff(f_125, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 14.17/5.89  tff(f_156, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 14.17/5.89  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 14.17/5.89  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 14.17/5.89  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.17/5.89  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 14.17/5.89  tff(f_94, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 14.17/5.89  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.17/5.89  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.17/5.89  tff(c_60, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.17/5.89  tff(c_44, plain, (![A_44]: (l1_struct_0(A_44) | ~l1_orders_2(A_44))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.17/5.89  tff(c_103, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.17/5.89  tff(c_115, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_orders_2(A_68))), inference(resolution, [status(thm)], [c_44, c_103])).
% 14.17/5.89  tff(c_119, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_115])).
% 14.17/5.89  tff(c_66, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.17/5.89  tff(c_64, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.17/5.89  tff(c_62, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.17/5.89  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.17/5.89  tff(c_481, plain, (![A_141, B_142]: (k1_orders_2(A_141, B_142)=a_2_0_orders_2(A_141, B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.17/5.89  tff(c_496, plain, (![B_142]: (k1_orders_2('#skF_4', B_142)=a_2_0_orders_2('#skF_4', B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_481])).
% 14.17/5.89  tff(c_505, plain, (![B_142]: (k1_orders_2('#skF_4', B_142)=a_2_0_orders_2('#skF_4', B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_496])).
% 14.17/5.89  tff(c_508, plain, (![B_143]: (k1_orders_2('#skF_4', B_143)=a_2_0_orders_2('#skF_4', B_143) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_505])).
% 14.17/5.89  tff(c_533, plain, (![A_144]: (k1_orders_2('#skF_4', A_144)=a_2_0_orders_2('#skF_4', A_144) | ~r1_tarski(A_144, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_22, c_508])).
% 14.17/5.89  tff(c_549, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_533])).
% 14.17/5.89  tff(c_58, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.17/5.89  tff(c_567, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_549, c_58])).
% 14.17/5.89  tff(c_26, plain, (![A_17]: (r2_hidden('#skF_1'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.17/5.89  tff(c_191, plain, (![C_89, A_90, B_91]: (r2_hidden(C_89, A_90) | ~r2_hidden(C_89, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.17/5.89  tff(c_200, plain, (![A_99, A_100]: (r2_hidden('#skF_1'(A_99), A_100) | ~m1_subset_1(A_99, k1_zfmisc_1(A_100)) | k1_xboole_0=A_99)), inference(resolution, [status(thm)], [c_26, c_191])).
% 14.17/5.89  tff(c_16, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.17/5.89  tff(c_3327, plain, (![A_283, A_284, A_285]: (r2_hidden('#skF_1'(A_283), A_284) | ~m1_subset_1(A_285, k1_zfmisc_1(A_284)) | ~m1_subset_1(A_283, k1_zfmisc_1(A_285)) | k1_xboole_0=A_283)), inference(resolution, [status(thm)], [c_200, c_16])).
% 14.17/5.89  tff(c_3712, plain, (![A_298, B_299, A_300]: (r2_hidden('#skF_1'(A_298), B_299) | ~m1_subset_1(A_298, k1_zfmisc_1(A_300)) | k1_xboole_0=A_298 | ~r1_tarski(A_300, B_299))), inference(resolution, [status(thm)], [c_22, c_3327])).
% 14.17/5.89  tff(c_3772, plain, (![A_301, B_302, B_303]: (r2_hidden('#skF_1'(A_301), B_302) | k1_xboole_0=A_301 | ~r1_tarski(B_303, B_302) | ~r1_tarski(A_301, B_303))), inference(resolution, [status(thm)], [c_22, c_3712])).
% 14.17/5.89  tff(c_3812, plain, (![A_301, B_2]: (r2_hidden('#skF_1'(A_301), B_2) | k1_xboole_0=A_301 | ~r1_tarski(A_301, B_2))), inference(resolution, [status(thm)], [c_6, c_3772])).
% 14.17/5.89  tff(c_623, plain, (![A_152, B_153]: (m1_subset_1(k1_orders_2(A_152, B_153), k1_zfmisc_1(u1_struct_0(A_152))) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_125])).
% 14.17/5.89  tff(c_636, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_549, c_623])).
% 14.17/5.89  tff(c_648, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_119, c_119, c_636])).
% 14.17/5.89  tff(c_649, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_648])).
% 14.17/5.89  tff(c_798, plain, (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_649])).
% 14.17/5.89  tff(c_801, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_798])).
% 14.17/5.89  tff(c_805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_801])).
% 14.17/5.89  tff(c_807, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_649])).
% 14.17/5.89  tff(c_761, plain, (![A_156, B_157, C_158]: ('#skF_2'(A_156, B_157, C_158)=A_156 | ~r2_hidden(A_156, a_2_0_orders_2(B_157, C_158)) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(B_157))) | ~l1_orders_2(B_157) | ~v5_orders_2(B_157) | ~v4_orders_2(B_157) | ~v3_orders_2(B_157) | v2_struct_0(B_157))), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.17/5.89  tff(c_3813, plain, (![B_304, C_305]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_304, C_305)), B_304, C_305)='#skF_1'(a_2_0_orders_2(B_304, C_305)) | ~m1_subset_1(C_305, k1_zfmisc_1(u1_struct_0(B_304))) | ~l1_orders_2(B_304) | ~v5_orders_2(B_304) | ~v4_orders_2(B_304) | ~v3_orders_2(B_304) | v2_struct_0(B_304) | a_2_0_orders_2(B_304, C_305)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_761])).
% 14.17/5.89  tff(c_3838, plain, (![C_305]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_305)), '#skF_4', C_305)='#skF_1'(a_2_0_orders_2('#skF_4', C_305)) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_305)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_119, c_3813])).
% 14.17/5.89  tff(c_3851, plain, (![C_305]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_305)), '#skF_4', C_305)='#skF_1'(a_2_0_orders_2('#skF_4', C_305)) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_305)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_3838])).
% 14.17/5.89  tff(c_3997, plain, (![C_312]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_312)), '#skF_4', C_312)='#skF_1'(a_2_0_orders_2('#skF_4', C_312)) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', C_312)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_68, c_3851])).
% 14.17/5.89  tff(c_4015, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_807, c_3997])).
% 14.17/5.89  tff(c_4042, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_567, c_4015])).
% 14.17/5.89  tff(c_1345, plain, (![B_202, E_203, A_204, C_205]: (r2_orders_2(B_202, E_203, '#skF_2'(A_204, B_202, C_205)) | ~r2_hidden(E_203, C_205) | ~m1_subset_1(E_203, u1_struct_0(B_202)) | ~r2_hidden(A_204, a_2_0_orders_2(B_202, C_205)) | ~m1_subset_1(C_205, k1_zfmisc_1(u1_struct_0(B_202))) | ~l1_orders_2(B_202) | ~v5_orders_2(B_202) | ~v4_orders_2(B_202) | ~v3_orders_2(B_202) | v2_struct_0(B_202))), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.17/5.89  tff(c_1365, plain, (![B_202, E_203, A_204, A_12]: (r2_orders_2(B_202, E_203, '#skF_2'(A_204, B_202, A_12)) | ~r2_hidden(E_203, A_12) | ~m1_subset_1(E_203, u1_struct_0(B_202)) | ~r2_hidden(A_204, a_2_0_orders_2(B_202, A_12)) | ~l1_orders_2(B_202) | ~v5_orders_2(B_202) | ~v4_orders_2(B_202) | ~v3_orders_2(B_202) | v2_struct_0(B_202) | ~r1_tarski(A_12, u1_struct_0(B_202)))), inference(resolution, [status(thm)], [c_22, c_1345])).
% 14.17/5.89  tff(c_5031, plain, (![E_203]: (r2_orders_2('#skF_4', E_203, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_203, k2_struct_0('#skF_4')) | ~m1_subset_1(E_203, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4042, c_1365])).
% 14.17/5.89  tff(c_5041, plain, (![E_203]: (r2_orders_2('#skF_4', E_203, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_203, k2_struct_0('#skF_4')) | ~m1_subset_1(E_203, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_119, c_66, c_64, c_62, c_60, c_119, c_5031])).
% 14.17/5.89  tff(c_5042, plain, (![E_203]: (r2_orders_2('#skF_4', E_203, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_203, k2_struct_0('#skF_4')) | ~m1_subset_1(E_203, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_5041])).
% 14.17/5.89  tff(c_7216, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_5042])).
% 14.17/5.89  tff(c_7219, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~r1_tarski(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3812, c_7216])).
% 14.17/5.89  tff(c_7234, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7219])).
% 14.17/5.89  tff(c_7236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_567, c_7234])).
% 14.17/5.89  tff(c_7238, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_5042])).
% 14.17/5.89  tff(c_806, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_649])).
% 14.17/5.89  tff(c_24, plain, (![A_14, C_16, B_15]: (m1_subset_1(A_14, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.17/5.89  tff(c_910, plain, (![A_166]: (m1_subset_1(A_166, k2_struct_0('#skF_4')) | ~r2_hidden(A_166, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_806, c_24])).
% 14.17/5.89  tff(c_918, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_910])).
% 14.17/5.89  tff(c_922, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_567, c_918])).
% 14.17/5.89  tff(c_18, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.17/5.89  tff(c_528, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_508])).
% 14.17/5.89  tff(c_639, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_528, c_623])).
% 14.17/5.89  tff(c_651, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_18, c_119, c_639])).
% 14.17/5.89  tff(c_652, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_651])).
% 14.17/5.89  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.17/5.89  tff(c_95, plain, (![A_63, B_64]: (~r2_hidden(A_63, k2_zfmisc_1(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.17/5.89  tff(c_101, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_95])).
% 14.17/5.89  tff(c_1040, plain, (![D_172, B_173, C_174]: (r2_hidden('#skF_3'(D_172, B_173, C_174, D_172), C_174) | r2_hidden(D_172, a_2_0_orders_2(B_173, C_174)) | ~m1_subset_1(D_172, u1_struct_0(B_173)) | ~m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(B_173))) | ~l1_orders_2(B_173) | ~v5_orders_2(B_173) | ~v4_orders_2(B_173) | ~v3_orders_2(B_173) | v2_struct_0(B_173))), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.17/5.89  tff(c_1053, plain, (![D_172, C_174]: (r2_hidden('#skF_3'(D_172, '#skF_4', C_174, D_172), C_174) | r2_hidden(D_172, a_2_0_orders_2('#skF_4', C_174)) | ~m1_subset_1(D_172, u1_struct_0('#skF_4')) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_1040])).
% 14.17/5.89  tff(c_1062, plain, (![D_172, C_174]: (r2_hidden('#skF_3'(D_172, '#skF_4', C_174, D_172), C_174) | r2_hidden(D_172, a_2_0_orders_2('#skF_4', C_174)) | ~m1_subset_1(D_172, k2_struct_0('#skF_4')) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_119, c_1053])).
% 14.17/5.89  tff(c_1155, plain, (![D_181, C_182]: (r2_hidden('#skF_3'(D_181, '#skF_4', C_182, D_181), C_182) | r2_hidden(D_181, a_2_0_orders_2('#skF_4', C_182)) | ~m1_subset_1(D_181, k2_struct_0('#skF_4')) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_1062])).
% 14.17/5.89  tff(c_1179, plain, (![D_181]: (r2_hidden('#skF_3'(D_181, '#skF_4', k1_xboole_0, D_181), k1_xboole_0) | r2_hidden(D_181, a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_181, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_18, c_1155])).
% 14.17/5.89  tff(c_1192, plain, (![D_183]: (r2_hidden(D_183, a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_183, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_101, c_1179])).
% 14.17/5.89  tff(c_1309, plain, (![D_199, A_200]: (r2_hidden(D_199, A_200) | ~m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(A_200)) | ~m1_subset_1(D_199, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1192, c_16])).
% 14.17/5.89  tff(c_1320, plain, (![D_201]: (r2_hidden(D_201, k2_struct_0('#skF_4')) | ~m1_subset_1(D_201, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_652, c_1309])).
% 14.17/5.89  tff(c_1597, plain, (![D_224, A_225]: (r2_hidden(D_224, A_225) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(A_225)) | ~m1_subset_1(D_224, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1320, c_16])).
% 14.17/5.89  tff(c_1608, plain, (![D_226, B_227]: (r2_hidden(D_226, B_227) | ~m1_subset_1(D_226, k2_struct_0('#skF_4')) | ~r1_tarski(k2_struct_0('#skF_4'), B_227))), inference(resolution, [status(thm)], [c_22, c_1597])).
% 14.17/5.89  tff(c_1852, plain, (![B_235]: (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), B_235) | ~r1_tarski(k2_struct_0('#skF_4'), B_235))), inference(resolution, [status(thm)], [c_922, c_1608])).
% 14.17/5.89  tff(c_9318, plain, (![A_503, B_504]: (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), A_503) | ~m1_subset_1(B_504, k1_zfmisc_1(A_503)) | ~r1_tarski(k2_struct_0('#skF_4'), B_504))), inference(resolution, [status(thm)], [c_1852, c_16])).
% 14.17/5.89  tff(c_9357, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_807, c_9318])).
% 14.17/5.89  tff(c_9391, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9357])).
% 14.17/5.89  tff(c_4171, plain, (![B_319, E_320, A_321, A_322]: (r2_orders_2(B_319, E_320, '#skF_2'(A_321, B_319, A_322)) | ~r2_hidden(E_320, A_322) | ~m1_subset_1(E_320, u1_struct_0(B_319)) | ~r2_hidden(A_321, a_2_0_orders_2(B_319, A_322)) | ~l1_orders_2(B_319) | ~v5_orders_2(B_319) | ~v4_orders_2(B_319) | ~v3_orders_2(B_319) | v2_struct_0(B_319) | ~r1_tarski(A_322, u1_struct_0(B_319)))), inference(resolution, [status(thm)], [c_22, c_1345])).
% 14.17/5.89  tff(c_36, plain, (![A_32, C_38]: (~r2_orders_2(A_32, C_38, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~l1_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 14.17/5.89  tff(c_11346, plain, (![A_587, B_588, A_589]: (~r2_hidden('#skF_2'(A_587, B_588, A_589), A_589) | ~m1_subset_1('#skF_2'(A_587, B_588, A_589), u1_struct_0(B_588)) | ~r2_hidden(A_587, a_2_0_orders_2(B_588, A_589)) | ~l1_orders_2(B_588) | ~v5_orders_2(B_588) | ~v4_orders_2(B_588) | ~v3_orders_2(B_588) | v2_struct_0(B_588) | ~r1_tarski(A_589, u1_struct_0(B_588)))), inference(resolution, [status(thm)], [c_4171, c_36])).
% 14.17/5.89  tff(c_11356, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4042, c_11346])).
% 14.17/5.89  tff(c_11379, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_119, c_66, c_64, c_62, c_60, c_7238, c_922, c_119, c_4042, c_9391, c_11356])).
% 14.17/5.89  tff(c_11381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_11379])).
% 14.17/5.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.17/5.89  
% 14.17/5.89  Inference rules
% 14.17/5.89  ----------------------
% 14.17/5.89  #Ref     : 0
% 14.17/5.89  #Sup     : 2537
% 14.17/5.89  #Fact    : 0
% 14.17/5.89  #Define  : 0
% 14.17/5.89  #Split   : 22
% 14.17/5.89  #Chain   : 0
% 14.17/5.89  #Close   : 0
% 14.17/5.89  
% 14.17/5.89  Ordering : KBO
% 14.17/5.89  
% 14.17/5.89  Simplification rules
% 14.17/5.89  ----------------------
% 14.17/5.89  #Subsume      : 488
% 14.17/5.89  #Demod        : 1695
% 14.17/5.89  #Tautology    : 402
% 14.17/5.89  #SimpNegUnit  : 266
% 14.17/5.89  #BackRed      : 108
% 14.17/5.89  
% 14.17/5.89  #Partial instantiations: 0
% 14.17/5.89  #Strategies tried      : 1
% 14.17/5.89  
% 14.17/5.89  Timing (in seconds)
% 14.17/5.89  ----------------------
% 14.17/5.90  Preprocessing        : 0.58
% 14.17/5.90  Parsing              : 0.30
% 14.17/5.90  CNF conversion       : 0.05
% 14.17/5.90  Main loop            : 4.49
% 14.17/5.90  Inferencing          : 1.04
% 14.17/5.90  Reduction            : 1.38
% 14.17/5.90  Demodulation         : 0.92
% 14.17/5.90  BG Simplification    : 0.15
% 14.17/5.90  Subsumption          : 1.56
% 14.17/5.90  Abstraction          : 0.17
% 14.17/5.90  MUC search           : 0.00
% 14.17/5.90  Cooper               : 0.00
% 14.17/5.90  Total                : 5.15
% 14.17/5.90  Index Insertion      : 0.00
% 14.17/5.90  Index Deletion       : 0.00
% 14.17/5.90  Index Matching       : 0.00
% 14.17/5.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
