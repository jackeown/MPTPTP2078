%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:56 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 316 expanded)
%              Number of leaves         :   48 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :  314 (1294 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_mcart_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_279,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_159,axiom,(
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

tff(f_178,axiom,(
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

tff(f_203,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_121,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_226,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_254,axiom,(
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

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_90,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_88,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_86,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_84,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_82,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_80,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_1178,plain,(
    ! [C_354,A_355,B_356] :
      ( m1_subset_1(C_354,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ m2_orders_2(C_354,A_355,B_356)
      | ~ m1_orders_1(B_356,k1_orders_1(u1_struct_0(A_355)))
      | ~ l1_orders_2(A_355)
      | ~ v5_orders_2(A_355)
      | ~ v4_orders_2(A_355)
      | ~ v3_orders_2(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1180,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1178])).

tff(c_1183,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_1180])).

tff(c_1184,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1183])).

tff(c_239,plain,(
    ! [A_158,B_159] :
      ( r2_xboole_0(A_158,B_159)
      | B_159 = A_158
      | ~ r1_tarski(A_158,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_153,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_94,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_163,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_94])).

tff(c_250,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_239,c_163])).

tff(c_256,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_632,plain,(
    ! [C_245,B_246,A_247] :
      ( r1_tarski(C_245,B_246)
      | ~ m1_orders_2(C_245,A_247,B_246)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_orders_2(A_247)
      | ~ v5_orders_2(A_247)
      | ~ v4_orders_2(A_247)
      | ~ v3_orders_2(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_634,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_153,c_632])).

tff(c_637,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_634])).

tff(c_638,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_256,c_637])).

tff(c_78,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_750,plain,(
    ! [C_258,A_259,B_260] :
      ( m1_subset_1(C_258,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ m2_orders_2(C_258,A_259,B_260)
      | ~ m1_orders_1(B_260,k1_orders_1(u1_struct_0(A_259)))
      | ~ l1_orders_2(A_259)
      | ~ v5_orders_2(A_259)
      | ~ v4_orders_2(A_259)
      | ~ v3_orders_2(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_754,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_750])).

tff(c_761,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_754])).

tff(c_763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_638,c_761])).

tff(c_764,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_767,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_153])).

tff(c_1366,plain,(
    ! [C_371,A_372,B_373] :
      ( ~ m1_orders_2(C_371,A_372,B_373)
      | ~ m1_orders_2(B_373,A_372,C_371)
      | k1_xboole_0 = B_373
      | ~ m1_subset_1(C_371,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ m1_subset_1(B_373,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ l1_orders_2(A_372)
      | ~ v5_orders_2(A_372)
      | ~ v4_orders_2(A_372)
      | ~ v3_orders_2(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1368,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_767,c_1366])).

tff(c_1371,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_1184,c_767,c_1368])).

tff(c_1372,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1371])).

tff(c_902,plain,(
    ! [A_288,B_289,C_290] :
      ( r1_tarski(k4_xboole_0(A_288,B_289),C_290)
      | ~ r1_tarski(A_288,k2_xboole_0(B_289,C_290)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_1'(A_39),A_39)
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_155,plain,(
    ! [B_134,A_135] :
      ( ~ r1_tarski(B_134,A_135)
      | ~ r2_hidden(A_135,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_159,plain,(
    ! [A_39] :
      ( ~ r1_tarski(A_39,'#skF_1'(A_39))
      | k1_xboole_0 = A_39 ) ),
    inference(resolution,[status(thm)],[c_56,c_155])).

tff(c_914,plain,(
    ! [A_288,B_289] :
      ( k4_xboole_0(A_288,B_289) = k1_xboole_0
      | ~ r1_tarski(A_288,k2_xboole_0(B_289,'#skF_1'(k4_xboole_0(A_288,B_289)))) ) ),
    inference(resolution,[status(thm)],[c_902,c_159])).

tff(c_5212,plain,(
    ! [A_799,B_800] :
      ( k4_xboole_0(A_799,B_800) = '#skF_4'
      | ~ r1_tarski(A_799,k2_xboole_0(B_800,'#skF_1'(k4_xboole_0(A_799,B_800)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_914])).

tff(c_5262,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_5212])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1248,plain,(
    ! [C_362,D_363,A_364,B_365] :
      ( ~ r1_xboole_0(C_362,D_363)
      | ~ m2_orders_2(D_363,A_364,B_365)
      | ~ m2_orders_2(C_362,A_364,B_365)
      | ~ m1_orders_1(B_365,k1_orders_1(u1_struct_0(A_364)))
      | ~ l1_orders_2(A_364)
      | ~ v5_orders_2(A_364)
      | ~ v4_orders_2(A_364)
      | ~ v3_orders_2(A_364)
      | v2_struct_0(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_2312,plain,(
    ! [B_488,A_489,B_490,A_491] :
      ( ~ m2_orders_2(B_488,A_489,B_490)
      | ~ m2_orders_2(A_491,A_489,B_490)
      | ~ m1_orders_1(B_490,k1_orders_1(u1_struct_0(A_489)))
      | ~ l1_orders_2(A_489)
      | ~ v5_orders_2(A_489)
      | ~ v4_orders_2(A_489)
      | ~ v3_orders_2(A_489)
      | v2_struct_0(A_489)
      | k4_xboole_0(A_491,B_488) != A_491 ) ),
    inference(resolution,[status(thm)],[c_26,c_1248])).

tff(c_2314,plain,(
    ! [A_491] :
      ( ~ m2_orders_2(A_491,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k4_xboole_0(A_491,'#skF_4') != A_491 ) ),
    inference(resolution,[status(thm)],[c_80,c_2312])).

tff(c_2317,plain,(
    ! [A_491] :
      ( ~ m2_orders_2(A_491,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2')
      | k4_xboole_0(A_491,'#skF_4') != A_491 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_2314])).

tff(c_2323,plain,(
    ! [A_492] :
      ( ~ m2_orders_2(A_492,'#skF_2','#skF_3')
      | k4_xboole_0(A_492,'#skF_4') != A_492 ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2317])).

tff(c_2327,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_80,c_2323])).

tff(c_5265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5262,c_2327])).

tff(c_5266,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5271,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_5266,c_6])).

tff(c_5382,plain,(
    ! [B_833,A_834] :
      ( B_833 = A_834
      | ~ r1_tarski(B_833,A_834)
      | ~ r1_tarski(A_834,B_833) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5396,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5271,c_5382])).

tff(c_5404,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5396])).

tff(c_6095,plain,(
    ! [C_953,A_954,B_955] :
      ( m1_subset_1(C_953,k1_zfmisc_1(u1_struct_0(A_954)))
      | ~ m2_orders_2(C_953,A_954,B_955)
      | ~ m1_orders_1(B_955,k1_orders_1(u1_struct_0(A_954)))
      | ~ l1_orders_2(A_954)
      | ~ v5_orders_2(A_954)
      | ~ v4_orders_2(A_954)
      | ~ v3_orders_2(A_954)
      | v2_struct_0(A_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_6097,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_6095])).

tff(c_6102,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_6097])).

tff(c_6103,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_6102])).

tff(c_16,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5273,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5266,c_94])).

tff(c_6389,plain,(
    ! [C_1000,A_1001,D_1002,B_1003] :
      ( m1_orders_2(C_1000,A_1001,D_1002)
      | m1_orders_2(D_1002,A_1001,C_1000)
      | D_1002 = C_1000
      | ~ m2_orders_2(D_1002,A_1001,B_1003)
      | ~ m2_orders_2(C_1000,A_1001,B_1003)
      | ~ m1_orders_1(B_1003,k1_orders_1(u1_struct_0(A_1001)))
      | ~ l1_orders_2(A_1001)
      | ~ v5_orders_2(A_1001)
      | ~ v4_orders_2(A_1001)
      | ~ v3_orders_2(A_1001)
      | v2_struct_0(A_1001) ) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_6391,plain,(
    ! [C_1000] :
      ( m1_orders_2(C_1000,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_1000)
      | C_1000 = '#skF_4'
      | ~ m2_orders_2(C_1000,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_80,c_6389])).

tff(c_6396,plain,(
    ! [C_1000] :
      ( m1_orders_2(C_1000,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_1000)
      | C_1000 = '#skF_4'
      | ~ m2_orders_2(C_1000,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_6391])).

tff(c_6459,plain,(
    ! [C_1012] :
      ( m1_orders_2(C_1012,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_1012)
      | C_1012 = '#skF_4'
      | ~ m2_orders_2(C_1012,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_6396])).

tff(c_6465,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_78,c_6459])).

tff(c_6470,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5273,c_6465])).

tff(c_6471,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6470])).

tff(c_6495,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6471,c_5404])).

tff(c_6505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6495])).

tff(c_6506,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6470])).

tff(c_68,plain,(
    ! [C_71,B_69,A_65] :
      ( r1_tarski(C_71,B_69)
      | ~ m1_orders_2(C_71,A_65,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_6515,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6506,c_68])).

tff(c_6530,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_6103,c_6515])).

tff(c_6532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5404,c_6530])).

tff(c_6533,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5396])).

tff(c_6537,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6533,c_5266])).

tff(c_6541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_6537])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:01:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.32/2.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/2.55  
% 7.32/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/2.55  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_mcart_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 7.32/2.55  
% 7.32/2.55  %Foreground sorts:
% 7.32/2.55  
% 7.32/2.55  
% 7.32/2.55  %Background operators:
% 7.32/2.55  
% 7.32/2.55  
% 7.32/2.55  %Foreground operators:
% 7.32/2.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.32/2.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.32/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.32/2.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.32/2.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.32/2.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.32/2.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.32/2.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.32/2.55  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 7.32/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.32/2.55  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 7.32/2.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.32/2.55  tff('#skF_5', type, '#skF_5': $i).
% 7.32/2.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.32/2.55  tff('#skF_2', type, '#skF_2': $i).
% 7.32/2.55  tff('#skF_3', type, '#skF_3': $i).
% 7.32/2.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.32/2.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.32/2.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.32/2.55  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 7.32/2.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.32/2.55  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 7.32/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.32/2.55  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 7.32/2.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.32/2.55  tff('#skF_4', type, '#skF_4': $i).
% 7.32/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.32/2.55  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 7.32/2.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.32/2.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.32/2.55  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 7.32/2.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.32/2.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.32/2.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.32/2.55  
% 7.53/2.57  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 7.53/2.57  tff(f_279, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 7.53/2.57  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.53/2.57  tff(f_159, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 7.53/2.57  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 7.53/2.57  tff(f_178, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 7.53/2.57  tff(f_203, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 7.53/2.57  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.53/2.57  tff(f_121, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 7.53/2.57  tff(f_105, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.53/2.57  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.53/2.57  tff(f_226, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 7.53/2.57  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.53/2.57  tff(f_254, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 7.53/2.57  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.53/2.57  tff(c_92, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.53/2.57  tff(c_90, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_88, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_86, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_84, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_82, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_80, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_1178, plain, (![C_354, A_355, B_356]: (m1_subset_1(C_354, k1_zfmisc_1(u1_struct_0(A_355))) | ~m2_orders_2(C_354, A_355, B_356) | ~m1_orders_1(B_356, k1_orders_1(u1_struct_0(A_355))) | ~l1_orders_2(A_355) | ~v5_orders_2(A_355) | ~v4_orders_2(A_355) | ~v3_orders_2(A_355) | v2_struct_0(A_355))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.53/2.57  tff(c_1180, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1178])).
% 7.53/2.57  tff(c_1183, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_1180])).
% 7.53/2.57  tff(c_1184, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_92, c_1183])).
% 7.53/2.57  tff(c_239, plain, (![A_158, B_159]: (r2_xboole_0(A_158, B_159) | B_159=A_158 | ~r1_tarski(A_158, B_159))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.53/2.57  tff(c_100, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_153, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_100])).
% 7.53/2.57  tff(c_94, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_163, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_94])).
% 7.53/2.57  tff(c_250, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_239, c_163])).
% 7.53/2.57  tff(c_256, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_250])).
% 7.53/2.57  tff(c_632, plain, (![C_245, B_246, A_247]: (r1_tarski(C_245, B_246) | ~m1_orders_2(C_245, A_247, B_246) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_orders_2(A_247) | ~v5_orders_2(A_247) | ~v4_orders_2(A_247) | ~v3_orders_2(A_247) | v2_struct_0(A_247))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.53/2.57  tff(c_634, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_153, c_632])).
% 7.53/2.57  tff(c_637, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_634])).
% 7.53/2.57  tff(c_638, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_92, c_256, c_637])).
% 7.53/2.57  tff(c_78, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_279])).
% 7.53/2.57  tff(c_750, plain, (![C_258, A_259, B_260]: (m1_subset_1(C_258, k1_zfmisc_1(u1_struct_0(A_259))) | ~m2_orders_2(C_258, A_259, B_260) | ~m1_orders_1(B_260, k1_orders_1(u1_struct_0(A_259))) | ~l1_orders_2(A_259) | ~v5_orders_2(A_259) | ~v4_orders_2(A_259) | ~v3_orders_2(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.53/2.57  tff(c_754, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_750])).
% 7.53/2.57  tff(c_761, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_754])).
% 7.53/2.57  tff(c_763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_638, c_761])).
% 7.53/2.57  tff(c_764, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_250])).
% 7.53/2.57  tff(c_767, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_764, c_153])).
% 7.53/2.57  tff(c_1366, plain, (![C_371, A_372, B_373]: (~m1_orders_2(C_371, A_372, B_373) | ~m1_orders_2(B_373, A_372, C_371) | k1_xboole_0=B_373 | ~m1_subset_1(C_371, k1_zfmisc_1(u1_struct_0(A_372))) | ~m1_subset_1(B_373, k1_zfmisc_1(u1_struct_0(A_372))) | ~l1_orders_2(A_372) | ~v5_orders_2(A_372) | ~v4_orders_2(A_372) | ~v3_orders_2(A_372) | v2_struct_0(A_372))), inference(cnfTransformation, [status(thm)], [f_203])).
% 7.53/2.57  tff(c_1368, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_767, c_1366])).
% 7.53/2.57  tff(c_1371, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_1184, c_767, c_1368])).
% 7.53/2.57  tff(c_1372, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_92, c_1371])).
% 7.53/2.57  tff(c_902, plain, (![A_288, B_289, C_290]: (r1_tarski(k4_xboole_0(A_288, B_289), C_290) | ~r1_tarski(A_288, k2_xboole_0(B_289, C_290)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.53/2.57  tff(c_56, plain, (![A_39]: (r2_hidden('#skF_1'(A_39), A_39) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.53/2.57  tff(c_155, plain, (![B_134, A_135]: (~r1_tarski(B_134, A_135) | ~r2_hidden(A_135, B_134))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.53/2.57  tff(c_159, plain, (![A_39]: (~r1_tarski(A_39, '#skF_1'(A_39)) | k1_xboole_0=A_39)), inference(resolution, [status(thm)], [c_56, c_155])).
% 7.53/2.57  tff(c_914, plain, (![A_288, B_289]: (k4_xboole_0(A_288, B_289)=k1_xboole_0 | ~r1_tarski(A_288, k2_xboole_0(B_289, '#skF_1'(k4_xboole_0(A_288, B_289)))))), inference(resolution, [status(thm)], [c_902, c_159])).
% 7.53/2.57  tff(c_5212, plain, (![A_799, B_800]: (k4_xboole_0(A_799, B_800)='#skF_4' | ~r1_tarski(A_799, k2_xboole_0(B_800, '#skF_1'(k4_xboole_0(A_799, B_800)))))), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_914])).
% 7.53/2.57  tff(c_5262, plain, (![A_15]: (k4_xboole_0(A_15, A_15)='#skF_4')), inference(resolution, [status(thm)], [c_22, c_5212])).
% 7.53/2.57  tff(c_26, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.53/2.57  tff(c_1248, plain, (![C_362, D_363, A_364, B_365]: (~r1_xboole_0(C_362, D_363) | ~m2_orders_2(D_363, A_364, B_365) | ~m2_orders_2(C_362, A_364, B_365) | ~m1_orders_1(B_365, k1_orders_1(u1_struct_0(A_364))) | ~l1_orders_2(A_364) | ~v5_orders_2(A_364) | ~v4_orders_2(A_364) | ~v3_orders_2(A_364) | v2_struct_0(A_364))), inference(cnfTransformation, [status(thm)], [f_226])).
% 7.53/2.57  tff(c_2312, plain, (![B_488, A_489, B_490, A_491]: (~m2_orders_2(B_488, A_489, B_490) | ~m2_orders_2(A_491, A_489, B_490) | ~m1_orders_1(B_490, k1_orders_1(u1_struct_0(A_489))) | ~l1_orders_2(A_489) | ~v5_orders_2(A_489) | ~v4_orders_2(A_489) | ~v3_orders_2(A_489) | v2_struct_0(A_489) | k4_xboole_0(A_491, B_488)!=A_491)), inference(resolution, [status(thm)], [c_26, c_1248])).
% 7.53/2.57  tff(c_2314, plain, (![A_491]: (~m2_orders_2(A_491, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k4_xboole_0(A_491, '#skF_4')!=A_491)), inference(resolution, [status(thm)], [c_80, c_2312])).
% 7.53/2.57  tff(c_2317, plain, (![A_491]: (~m2_orders_2(A_491, '#skF_2', '#skF_3') | v2_struct_0('#skF_2') | k4_xboole_0(A_491, '#skF_4')!=A_491)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_2314])).
% 7.53/2.57  tff(c_2323, plain, (![A_492]: (~m2_orders_2(A_492, '#skF_2', '#skF_3') | k4_xboole_0(A_492, '#skF_4')!=A_492)), inference(negUnitSimplification, [status(thm)], [c_92, c_2317])).
% 7.53/2.57  tff(c_2327, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_80, c_2323])).
% 7.53/2.57  tff(c_5265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5262, c_2327])).
% 7.53/2.57  tff(c_5266, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_100])).
% 7.53/2.57  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.53/2.57  tff(c_5271, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_5266, c_6])).
% 7.53/2.57  tff(c_5382, plain, (![B_833, A_834]: (B_833=A_834 | ~r1_tarski(B_833, A_834) | ~r1_tarski(A_834, B_833))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.53/2.57  tff(c_5396, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5271, c_5382])).
% 7.53/2.57  tff(c_5404, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_5396])).
% 7.53/2.57  tff(c_6095, plain, (![C_953, A_954, B_955]: (m1_subset_1(C_953, k1_zfmisc_1(u1_struct_0(A_954))) | ~m2_orders_2(C_953, A_954, B_955) | ~m1_orders_1(B_955, k1_orders_1(u1_struct_0(A_954))) | ~l1_orders_2(A_954) | ~v5_orders_2(A_954) | ~v4_orders_2(A_954) | ~v3_orders_2(A_954) | v2_struct_0(A_954))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.53/2.57  tff(c_6097, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_6095])).
% 7.53/2.57  tff(c_6102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_6097])).
% 7.53/2.57  tff(c_6103, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_92, c_6102])).
% 7.53/2.57  tff(c_16, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.53/2.57  tff(c_5273, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5266, c_94])).
% 7.53/2.57  tff(c_6389, plain, (![C_1000, A_1001, D_1002, B_1003]: (m1_orders_2(C_1000, A_1001, D_1002) | m1_orders_2(D_1002, A_1001, C_1000) | D_1002=C_1000 | ~m2_orders_2(D_1002, A_1001, B_1003) | ~m2_orders_2(C_1000, A_1001, B_1003) | ~m1_orders_1(B_1003, k1_orders_1(u1_struct_0(A_1001))) | ~l1_orders_2(A_1001) | ~v5_orders_2(A_1001) | ~v4_orders_2(A_1001) | ~v3_orders_2(A_1001) | v2_struct_0(A_1001))), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.53/2.57  tff(c_6391, plain, (![C_1000]: (m1_orders_2(C_1000, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_1000) | C_1000='#skF_4' | ~m2_orders_2(C_1000, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_80, c_6389])).
% 7.53/2.57  tff(c_6396, plain, (![C_1000]: (m1_orders_2(C_1000, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_1000) | C_1000='#skF_4' | ~m2_orders_2(C_1000, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_6391])).
% 7.53/2.57  tff(c_6459, plain, (![C_1012]: (m1_orders_2(C_1012, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_1012) | C_1012='#skF_4' | ~m2_orders_2(C_1012, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_92, c_6396])).
% 7.53/2.57  tff(c_6465, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_78, c_6459])).
% 7.53/2.57  tff(c_6470, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5273, c_6465])).
% 7.53/2.57  tff(c_6471, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_6470])).
% 7.53/2.57  tff(c_6495, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6471, c_5404])).
% 7.53/2.57  tff(c_6505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_6495])).
% 7.53/2.57  tff(c_6506, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_6470])).
% 7.53/2.57  tff(c_68, plain, (![C_71, B_69, A_65]: (r1_tarski(C_71, B_69) | ~m1_orders_2(C_71, A_65, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.53/2.57  tff(c_6515, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6506, c_68])).
% 7.53/2.57  tff(c_6530, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_6103, c_6515])).
% 7.53/2.57  tff(c_6532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_5404, c_6530])).
% 7.53/2.57  tff(c_6533, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_5396])).
% 7.53/2.57  tff(c_6537, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6533, c_5266])).
% 7.53/2.57  tff(c_6541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_6537])).
% 7.53/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/2.57  
% 7.53/2.57  Inference rules
% 7.53/2.57  ----------------------
% 7.53/2.57  #Ref     : 0
% 7.53/2.57  #Sup     : 1423
% 7.53/2.57  #Fact    : 0
% 7.53/2.57  #Define  : 0
% 7.53/2.57  #Split   : 16
% 7.53/2.57  #Chain   : 0
% 7.53/2.57  #Close   : 0
% 7.53/2.57  
% 7.53/2.57  Ordering : KBO
% 7.53/2.57  
% 7.53/2.57  Simplification rules
% 7.53/2.57  ----------------------
% 7.53/2.57  #Subsume      : 296
% 7.53/2.57  #Demod        : 334
% 7.53/2.57  #Tautology    : 82
% 7.53/2.57  #SimpNegUnit  : 97
% 7.53/2.57  #BackRed      : 54
% 7.53/2.57  
% 7.53/2.57  #Partial instantiations: 0
% 7.53/2.57  #Strategies tried      : 1
% 7.53/2.57  
% 7.53/2.57  Timing (in seconds)
% 7.53/2.57  ----------------------
% 7.53/2.57  Preprocessing        : 0.39
% 7.53/2.57  Parsing              : 0.20
% 7.53/2.57  CNF conversion       : 0.03
% 7.53/2.57  Main loop            : 1.40
% 7.53/2.57  Inferencing          : 0.43
% 7.53/2.57  Reduction            : 0.44
% 7.53/2.57  Demodulation         : 0.27
% 7.53/2.57  BG Simplification    : 0.06
% 7.53/2.57  Subsumption          : 0.36
% 7.53/2.57  Abstraction          : 0.06
% 7.53/2.57  MUC search           : 0.00
% 7.53/2.57  Cooper               : 0.00
% 7.53/2.57  Total                : 1.83
% 7.53/2.57  Index Insertion      : 0.00
% 7.53/2.57  Index Deletion       : 0.00
% 7.53/2.57  Index Matching       : 0.00
% 7.53/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
