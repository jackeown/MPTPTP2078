%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:57 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 307 expanded)
%              Number of leaves         :   45 ( 131 expanded)
%              Depth                    :   11
%              Number of atoms          :  314 (1268 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_mcart_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_261,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_141,axiom,(
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

tff(f_160,axiom,(
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

tff(f_185,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_103,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_208,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_236,axiom,(
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

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_74,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_72,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_70,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_68,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_66,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_823,plain,(
    ! [C_297,A_298,B_299] :
      ( m1_subset_1(C_297,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ m2_orders_2(C_297,A_298,B_299)
      | ~ m1_orders_1(B_299,k1_orders_1(u1_struct_0(A_298)))
      | ~ l1_orders_2(A_298)
      | ~ v5_orders_2(A_298)
      | ~ v4_orders_2(A_298)
      | ~ v3_orders_2(A_298)
      | v2_struct_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_825,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_823])).

tff(c_828,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_825])).

tff(c_829,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_828])).

tff(c_150,plain,(
    ! [A_135,B_136] :
      ( r2_xboole_0(A_135,B_136)
      | B_136 = A_135
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_114,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_161,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_150,c_114])).

tff(c_167,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_86,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_126,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_86])).

tff(c_342,plain,(
    ! [C_193,B_194,A_195] :
      ( r1_tarski(C_193,B_194)
      | ~ m1_orders_2(C_193,A_195,B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_orders_2(A_195)
      | ~ v5_orders_2(A_195)
      | ~ v4_orders_2(A_195)
      | ~ v3_orders_2(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_344,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_126,c_342])).

tff(c_347,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_344])).

tff(c_348,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_167,c_347])).

tff(c_64,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_485,plain,(
    ! [C_215,A_216,B_217] :
      ( m1_subset_1(C_215,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ m2_orders_2(C_215,A_216,B_217)
      | ~ m1_orders_1(B_217,k1_orders_1(u1_struct_0(A_216)))
      | ~ l1_orders_2(A_216)
      | ~ v5_orders_2(A_216)
      | ~ v4_orders_2(A_216)
      | ~ v3_orders_2(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_489,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_485])).

tff(c_496,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_489])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_348,c_496])).

tff(c_499,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_501,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_126])).

tff(c_864,plain,(
    ! [C_306,A_307,B_308] :
      ( ~ m1_orders_2(C_306,A_307,B_308)
      | ~ m1_orders_2(B_308,A_307,C_306)
      | k1_xboole_0 = B_308
      | ~ m1_subset_1(C_306,k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ l1_orders_2(A_307)
      | ~ v5_orders_2(A_307)
      | ~ v4_orders_2(A_307)
      | ~ v3_orders_2(A_307)
      | v2_struct_0(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_866,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_501,c_864])).

tff(c_869,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_829,c_501,c_866])).

tff(c_870,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_869])).

tff(c_544,plain,(
    ! [A_229,B_230,C_231] :
      ( r1_tarski(k4_xboole_0(A_229,B_230),C_231)
      | ~ r1_tarski(A_229,k2_xboole_0(B_230,C_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_104,plain,(
    ! [B_118,A_119] :
      ( ~ r1_tarski(B_118,A_119)
      | ~ r2_hidden(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_108,plain,(
    ! [A_30] :
      ( ~ r1_tarski(A_30,'#skF_1'(A_30))
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_42,c_104])).

tff(c_556,plain,(
    ! [A_229,B_230] :
      ( k4_xboole_0(A_229,B_230) = k1_xboole_0
      | ~ r1_tarski(A_229,k2_xboole_0(B_230,'#skF_1'(k4_xboole_0(A_229,B_230)))) ) ),
    inference(resolution,[status(thm)],[c_544,c_108])).

tff(c_1666,plain,(
    ! [A_430,B_431] :
      ( k4_xboole_0(A_430,B_431) = '#skF_4'
      | ~ r1_tarski(A_430,k2_xboole_0(B_431,'#skF_1'(k4_xboole_0(A_430,B_431)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_556])).

tff(c_1701,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_1666])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_849,plain,(
    ! [C_300,D_301,A_302,B_303] :
      ( ~ r1_xboole_0(C_300,D_301)
      | ~ m2_orders_2(D_301,A_302,B_303)
      | ~ m2_orders_2(C_300,A_302,B_303)
      | ~ m1_orders_1(B_303,k1_orders_1(u1_struct_0(A_302)))
      | ~ l1_orders_2(A_302)
      | ~ v5_orders_2(A_302)
      | ~ v4_orders_2(A_302)
      | ~ v3_orders_2(A_302)
      | v2_struct_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1499,plain,(
    ! [B_412,A_413,B_414,A_415] :
      ( ~ m2_orders_2(B_412,A_413,B_414)
      | ~ m2_orders_2(A_415,A_413,B_414)
      | ~ m1_orders_1(B_414,k1_orders_1(u1_struct_0(A_413)))
      | ~ l1_orders_2(A_413)
      | ~ v5_orders_2(A_413)
      | ~ v4_orders_2(A_413)
      | ~ v3_orders_2(A_413)
      | v2_struct_0(A_413)
      | k4_xboole_0(A_415,B_412) != A_415 ) ),
    inference(resolution,[status(thm)],[c_26,c_849])).

tff(c_1501,plain,(
    ! [A_415] :
      ( ~ m2_orders_2(A_415,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k4_xboole_0(A_415,'#skF_4') != A_415 ) ),
    inference(resolution,[status(thm)],[c_66,c_1499])).

tff(c_1504,plain,(
    ! [A_415] :
      ( ~ m2_orders_2(A_415,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2')
      | k4_xboole_0(A_415,'#skF_4') != A_415 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_1501])).

tff(c_1537,plain,(
    ! [A_418] :
      ( ~ m2_orders_2(A_418,'#skF_2','#skF_3')
      | k4_xboole_0(A_418,'#skF_4') != A_418 ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1504])).

tff(c_1541,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_1537])).

tff(c_1704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_1541])).

tff(c_1706,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1710,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1706,c_6])).

tff(c_1749,plain,(
    ! [B_444,A_445] :
      ( B_444 = A_445
      | ~ r1_tarski(B_444,A_445)
      | ~ r1_tarski(A_445,B_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1756,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1710,c_1749])).

tff(c_1762,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1756])).

tff(c_2220,plain,(
    ! [C_544,A_545,B_546] :
      ( m1_subset_1(C_544,k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ m2_orders_2(C_544,A_545,B_546)
      | ~ m1_orders_1(B_546,k1_orders_1(u1_struct_0(A_545)))
      | ~ l1_orders_2(A_545)
      | ~ v5_orders_2(A_545)
      | ~ v4_orders_2(A_545)
      | ~ v3_orders_2(A_545)
      | v2_struct_0(A_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2222,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2220])).

tff(c_2227,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_2222])).

tff(c_2228,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2227])).

tff(c_16,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1705,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2566,plain,(
    ! [C_585,A_586,D_587,B_588] :
      ( m1_orders_2(C_585,A_586,D_587)
      | m1_orders_2(D_587,A_586,C_585)
      | D_587 = C_585
      | ~ m2_orders_2(D_587,A_586,B_588)
      | ~ m2_orders_2(C_585,A_586,B_588)
      | ~ m1_orders_1(B_588,k1_orders_1(u1_struct_0(A_586)))
      | ~ l1_orders_2(A_586)
      | ~ v5_orders_2(A_586)
      | ~ v4_orders_2(A_586)
      | ~ v3_orders_2(A_586)
      | v2_struct_0(A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_2570,plain,(
    ! [C_585] :
      ( m1_orders_2(C_585,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_585)
      | C_585 = '#skF_5'
      | ~ m2_orders_2(C_585,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_2566])).

tff(c_2577,plain,(
    ! [C_585] :
      ( m1_orders_2(C_585,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_585)
      | C_585 = '#skF_5'
      | ~ m2_orders_2(C_585,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_2570])).

tff(c_2627,plain,(
    ! [C_591] :
      ( m1_orders_2(C_591,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_591)
      | C_591 = '#skF_5'
      | ~ m2_orders_2(C_591,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2577])).

tff(c_2630,plain,
    ( m1_orders_2('#skF_4','#skF_2','#skF_5')
    | m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_2627])).

tff(c_2636,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1705,c_2630])).

tff(c_2639,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2636])).

tff(c_2680,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2639,c_1762])).

tff(c_2690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2680])).

tff(c_2691,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2636])).

tff(c_54,plain,(
    ! [C_58,B_56,A_52] :
      ( r1_tarski(C_58,B_56)
      | ~ m1_orders_2(C_58,A_52,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_orders_2(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2698,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2691,c_54])).

tff(c_2709,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2228,c_2698])).

tff(c_2711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1762,c_2709])).

tff(c_2712,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1756])).

tff(c_2716,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2712,c_1706])).

tff(c_2720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_2716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.01  
% 5.29/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.01  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_mcart_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.29/2.01  
% 5.29/2.01  %Foreground sorts:
% 5.29/2.01  
% 5.29/2.01  
% 5.29/2.01  %Background operators:
% 5.29/2.01  
% 5.29/2.01  
% 5.29/2.01  %Foreground operators:
% 5.29/2.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.29/2.01  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.29/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.29/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.29/2.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.29/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.29/2.01  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.29/2.01  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 5.29/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/2.01  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 5.29/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.29/2.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.29/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.29/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.29/2.01  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.29/2.01  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.29/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/2.01  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.29/2.01  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.29/2.01  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 5.29/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/2.01  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 5.29/2.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.29/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.29/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/2.01  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 5.29/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.29/2.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.29/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.29/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/2.01  
% 5.29/2.03  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 5.29/2.03  tff(f_261, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 5.29/2.03  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.29/2.03  tff(f_141, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 5.29/2.03  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.29/2.03  tff(f_160, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 5.29/2.03  tff(f_185, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 5.29/2.03  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.29/2.03  tff(f_103, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.29/2.03  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.29/2.03  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.29/2.03  tff(f_208, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 5.29/2.03  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.29/2.03  tff(f_236, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 5.29/2.03  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.29/2.03  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.29/2.03  tff(c_76, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_74, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_72, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_70, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_68, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_66, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_823, plain, (![C_297, A_298, B_299]: (m1_subset_1(C_297, k1_zfmisc_1(u1_struct_0(A_298))) | ~m2_orders_2(C_297, A_298, B_299) | ~m1_orders_1(B_299, k1_orders_1(u1_struct_0(A_298))) | ~l1_orders_2(A_298) | ~v5_orders_2(A_298) | ~v4_orders_2(A_298) | ~v3_orders_2(A_298) | v2_struct_0(A_298))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.29/2.03  tff(c_825, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_823])).
% 5.29/2.03  tff(c_828, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_825])).
% 5.29/2.03  tff(c_829, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_78, c_828])).
% 5.29/2.03  tff(c_150, plain, (![A_135, B_136]: (r2_xboole_0(A_135, B_136) | B_136=A_135 | ~r1_tarski(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/2.03  tff(c_80, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_114, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 5.29/2.03  tff(c_161, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_150, c_114])).
% 5.29/2.03  tff(c_167, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_161])).
% 5.29/2.03  tff(c_86, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_126, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_114, c_86])).
% 5.29/2.03  tff(c_342, plain, (![C_193, B_194, A_195]: (r1_tarski(C_193, B_194) | ~m1_orders_2(C_193, A_195, B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_orders_2(A_195) | ~v5_orders_2(A_195) | ~v4_orders_2(A_195) | ~v3_orders_2(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.29/2.03  tff(c_344, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_126, c_342])).
% 5.29/2.03  tff(c_347, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_344])).
% 5.29/2.03  tff(c_348, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_78, c_167, c_347])).
% 5.29/2.03  tff(c_64, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_261])).
% 5.29/2.03  tff(c_485, plain, (![C_215, A_216, B_217]: (m1_subset_1(C_215, k1_zfmisc_1(u1_struct_0(A_216))) | ~m2_orders_2(C_215, A_216, B_217) | ~m1_orders_1(B_217, k1_orders_1(u1_struct_0(A_216))) | ~l1_orders_2(A_216) | ~v5_orders_2(A_216) | ~v4_orders_2(A_216) | ~v3_orders_2(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.29/2.03  tff(c_489, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_485])).
% 5.29/2.03  tff(c_496, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_489])).
% 5.29/2.03  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_348, c_496])).
% 5.29/2.03  tff(c_499, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_161])).
% 5.29/2.03  tff(c_501, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_126])).
% 5.29/2.03  tff(c_864, plain, (![C_306, A_307, B_308]: (~m1_orders_2(C_306, A_307, B_308) | ~m1_orders_2(B_308, A_307, C_306) | k1_xboole_0=B_308 | ~m1_subset_1(C_306, k1_zfmisc_1(u1_struct_0(A_307))) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0(A_307))) | ~l1_orders_2(A_307) | ~v5_orders_2(A_307) | ~v4_orders_2(A_307) | ~v3_orders_2(A_307) | v2_struct_0(A_307))), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.29/2.03  tff(c_866, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_501, c_864])).
% 5.29/2.03  tff(c_869, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_829, c_501, c_866])).
% 5.29/2.03  tff(c_870, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_78, c_869])).
% 5.29/2.03  tff(c_544, plain, (![A_229, B_230, C_231]: (r1_tarski(k4_xboole_0(A_229, B_230), C_231) | ~r1_tarski(A_229, k2_xboole_0(B_230, C_231)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.29/2.03  tff(c_42, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.29/2.03  tff(c_104, plain, (![B_118, A_119]: (~r1_tarski(B_118, A_119) | ~r2_hidden(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.29/2.03  tff(c_108, plain, (![A_30]: (~r1_tarski(A_30, '#skF_1'(A_30)) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_42, c_104])).
% 5.29/2.03  tff(c_556, plain, (![A_229, B_230]: (k4_xboole_0(A_229, B_230)=k1_xboole_0 | ~r1_tarski(A_229, k2_xboole_0(B_230, '#skF_1'(k4_xboole_0(A_229, B_230)))))), inference(resolution, [status(thm)], [c_544, c_108])).
% 5.29/2.03  tff(c_1666, plain, (![A_430, B_431]: (k4_xboole_0(A_430, B_431)='#skF_4' | ~r1_tarski(A_430, k2_xboole_0(B_431, '#skF_1'(k4_xboole_0(A_430, B_431)))))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_556])).
% 5.29/2.03  tff(c_1701, plain, (![A_15]: (k4_xboole_0(A_15, A_15)='#skF_4')), inference(resolution, [status(thm)], [c_22, c_1666])).
% 5.29/2.03  tff(c_26, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.29/2.03  tff(c_849, plain, (![C_300, D_301, A_302, B_303]: (~r1_xboole_0(C_300, D_301) | ~m2_orders_2(D_301, A_302, B_303) | ~m2_orders_2(C_300, A_302, B_303) | ~m1_orders_1(B_303, k1_orders_1(u1_struct_0(A_302))) | ~l1_orders_2(A_302) | ~v5_orders_2(A_302) | ~v4_orders_2(A_302) | ~v3_orders_2(A_302) | v2_struct_0(A_302))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.29/2.03  tff(c_1499, plain, (![B_412, A_413, B_414, A_415]: (~m2_orders_2(B_412, A_413, B_414) | ~m2_orders_2(A_415, A_413, B_414) | ~m1_orders_1(B_414, k1_orders_1(u1_struct_0(A_413))) | ~l1_orders_2(A_413) | ~v5_orders_2(A_413) | ~v4_orders_2(A_413) | ~v3_orders_2(A_413) | v2_struct_0(A_413) | k4_xboole_0(A_415, B_412)!=A_415)), inference(resolution, [status(thm)], [c_26, c_849])).
% 5.29/2.03  tff(c_1501, plain, (![A_415]: (~m2_orders_2(A_415, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k4_xboole_0(A_415, '#skF_4')!=A_415)), inference(resolution, [status(thm)], [c_66, c_1499])).
% 5.29/2.03  tff(c_1504, plain, (![A_415]: (~m2_orders_2(A_415, '#skF_2', '#skF_3') | v2_struct_0('#skF_2') | k4_xboole_0(A_415, '#skF_4')!=A_415)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_1501])).
% 5.29/2.03  tff(c_1537, plain, (![A_418]: (~m2_orders_2(A_418, '#skF_2', '#skF_3') | k4_xboole_0(A_418, '#skF_4')!=A_418)), inference(negUnitSimplification, [status(thm)], [c_78, c_1504])).
% 5.29/2.03  tff(c_1541, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_66, c_1537])).
% 5.29/2.03  tff(c_1704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1701, c_1541])).
% 5.29/2.03  tff(c_1706, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_80])).
% 5.29/2.03  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/2.03  tff(c_1710, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1706, c_6])).
% 5.29/2.03  tff(c_1749, plain, (![B_444, A_445]: (B_444=A_445 | ~r1_tarski(B_444, A_445) | ~r1_tarski(A_445, B_444))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.29/2.03  tff(c_1756, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1710, c_1749])).
% 5.29/2.03  tff(c_1762, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1756])).
% 5.29/2.03  tff(c_2220, plain, (![C_544, A_545, B_546]: (m1_subset_1(C_544, k1_zfmisc_1(u1_struct_0(A_545))) | ~m2_orders_2(C_544, A_545, B_546) | ~m1_orders_1(B_546, k1_orders_1(u1_struct_0(A_545))) | ~l1_orders_2(A_545) | ~v5_orders_2(A_545) | ~v4_orders_2(A_545) | ~v3_orders_2(A_545) | v2_struct_0(A_545))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.29/2.03  tff(c_2222, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2220])).
% 5.29/2.03  tff(c_2227, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_2222])).
% 5.29/2.03  tff(c_2228, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_78, c_2227])).
% 5.29/2.03  tff(c_16, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.29/2.03  tff(c_1705, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_80])).
% 5.29/2.03  tff(c_2566, plain, (![C_585, A_586, D_587, B_588]: (m1_orders_2(C_585, A_586, D_587) | m1_orders_2(D_587, A_586, C_585) | D_587=C_585 | ~m2_orders_2(D_587, A_586, B_588) | ~m2_orders_2(C_585, A_586, B_588) | ~m1_orders_1(B_588, k1_orders_1(u1_struct_0(A_586))) | ~l1_orders_2(A_586) | ~v5_orders_2(A_586) | ~v4_orders_2(A_586) | ~v3_orders_2(A_586) | v2_struct_0(A_586))), inference(cnfTransformation, [status(thm)], [f_236])).
% 5.29/2.03  tff(c_2570, plain, (![C_585]: (m1_orders_2(C_585, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_585) | C_585='#skF_5' | ~m2_orders_2(C_585, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_2566])).
% 5.29/2.03  tff(c_2577, plain, (![C_585]: (m1_orders_2(C_585, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_585) | C_585='#skF_5' | ~m2_orders_2(C_585, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_2570])).
% 5.29/2.03  tff(c_2627, plain, (![C_591]: (m1_orders_2(C_591, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_591) | C_591='#skF_5' | ~m2_orders_2(C_591, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_78, c_2577])).
% 5.29/2.03  tff(c_2630, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_66, c_2627])).
% 5.29/2.03  tff(c_2636, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1705, c_2630])).
% 5.29/2.03  tff(c_2639, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_2636])).
% 5.29/2.03  tff(c_2680, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2639, c_1762])).
% 5.29/2.03  tff(c_2690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_2680])).
% 5.29/2.03  tff(c_2691, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_2636])).
% 5.29/2.03  tff(c_54, plain, (![C_58, B_56, A_52]: (r1_tarski(C_58, B_56) | ~m1_orders_2(C_58, A_52, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_orders_2(A_52) | ~v5_orders_2(A_52) | ~v4_orders_2(A_52) | ~v3_orders_2(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.29/2.03  tff(c_2698, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2691, c_54])).
% 5.29/2.03  tff(c_2709, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_2228, c_2698])).
% 5.29/2.03  tff(c_2711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1762, c_2709])).
% 5.29/2.03  tff(c_2712, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_1756])).
% 5.29/2.03  tff(c_2716, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2712, c_1706])).
% 5.29/2.03  tff(c_2720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_2716])).
% 5.29/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.03  
% 5.29/2.03  Inference rules
% 5.29/2.03  ----------------------
% 5.29/2.03  #Ref     : 0
% 5.29/2.03  #Sup     : 590
% 5.29/2.03  #Fact    : 0
% 5.29/2.03  #Define  : 0
% 5.29/2.03  #Split   : 14
% 5.29/2.03  #Chain   : 0
% 5.29/2.03  #Close   : 0
% 5.29/2.03  
% 5.29/2.03  Ordering : KBO
% 5.29/2.03  
% 5.29/2.03  Simplification rules
% 5.29/2.03  ----------------------
% 5.29/2.03  #Subsume      : 101
% 5.29/2.03  #Demod        : 244
% 5.29/2.03  #Tautology    : 38
% 5.29/2.03  #SimpNegUnit  : 57
% 5.29/2.03  #BackRed      : 67
% 5.29/2.03  
% 5.29/2.03  #Partial instantiations: 0
% 5.29/2.03  #Strategies tried      : 1
% 5.29/2.03  
% 5.29/2.03  Timing (in seconds)
% 5.29/2.03  ----------------------
% 5.29/2.03  Preprocessing        : 0.38
% 5.29/2.03  Parsing              : 0.22
% 5.29/2.03  CNF conversion       : 0.03
% 5.29/2.03  Main loop            : 0.83
% 5.29/2.03  Inferencing          : 0.29
% 5.29/2.03  Reduction            : 0.23
% 5.29/2.03  Demodulation         : 0.14
% 5.29/2.03  BG Simplification    : 0.04
% 5.29/2.03  Subsumption          : 0.20
% 5.29/2.03  Abstraction          : 0.04
% 5.29/2.03  MUC search           : 0.00
% 5.29/2.03  Cooper               : 0.00
% 5.29/2.04  Total                : 1.26
% 5.29/2.04  Index Insertion      : 0.00
% 5.29/2.04  Index Deletion       : 0.00
% 5.29/2.04  Index Matching       : 0.00
% 5.29/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
