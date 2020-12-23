%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:57 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 312 expanded)
%              Number of leaves         :   39 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 (1276 expanded)
%              Number of equality atoms :   33 (  61 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_221,negated_conjecture,(
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

tff(f_101,axiom,(
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

tff(f_120,axiom,(
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

tff(f_145,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_168,axiom,(
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

tff(f_196,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_58,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_56,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_54,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_52,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_50,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_46,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_794,plain,(
    ! [C_185,A_186,B_187] :
      ( m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ m2_orders_2(C_185,A_186,B_187)
      | ~ m1_orders_1(B_187,k1_orders_1(u1_struct_0(A_186)))
      | ~ l1_orders_2(A_186)
      | ~ v5_orders_2(A_186)
      | ~ v4_orders_2(A_186)
      | ~ v3_orders_2(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_796,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_794])).

tff(c_799,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_796])).

tff(c_800,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_799])).

tff(c_142,plain,(
    ! [A_105,B_106] :
      ( r2_xboole_0(A_105,B_106)
      | B_106 = A_105
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_132,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_153,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_132])).

tff(c_159,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_68,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_133,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_68])).

tff(c_374,plain,(
    ! [C_134,B_135,A_136] :
      ( r1_tarski(C_134,B_135)
      | ~ m1_orders_2(C_134,A_136,B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_376,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_133,c_374])).

tff(c_379,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_376])).

tff(c_380,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_159,c_379])).

tff(c_400,plain,(
    ! [C_140,A_141,B_142] :
      ( m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m2_orders_2(C_140,A_141,B_142)
      | ~ m1_orders_1(B_142,k1_orders_1(u1_struct_0(A_141)))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_402,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_400])).

tff(c_407,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_402])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_380,c_407])).

tff(c_410,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_412,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_133])).

tff(c_1023,plain,(
    ! [C_203,A_204,B_205] :
      ( ~ m1_orders_2(C_203,A_204,B_205)
      | ~ m1_orders_2(B_205,A_204,C_203)
      | k1_xboole_0 = B_205
      | ~ m1_subset_1(C_203,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_orders_2(A_204)
      | ~ v5_orders_2(A_204)
      | ~ v4_orders_2(A_204)
      | ~ v3_orders_2(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1025,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_412,c_1023])).

tff(c_1028,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_800,c_412,c_1025])).

tff(c_1029,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1028])).

tff(c_18,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,(
    ! [B_91,A_92] :
      ( r1_xboole_0(B_91,A_92)
      | ~ r1_xboole_0(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [B_17,A_16] : r1_xboole_0(B_17,k4_xboole_0(A_16,B_17)) ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_84,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,B_96) = A_95
      | ~ r1_xboole_0(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_91,plain,(
    ! [B_17,A_16] : k4_xboole_0(B_17,k4_xboole_0(A_16,B_17)) = B_17 ),
    inference(resolution,[status(thm)],[c_78,c_84])).

tff(c_128,plain,(
    ! [A_101,B_102] :
      ( k1_xboole_0 = A_101
      | ~ r1_tarski(A_101,k4_xboole_0(B_102,A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_839,plain,(
    ! [A_193,B_194] :
      ( k4_xboole_0(A_193,B_194) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_193,B_194),B_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_128])).

tff(c_857,plain,(
    ! [A_195] : k4_xboole_0(A_195,A_195) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_839])).

tff(c_918,plain,(
    ! [A_195] : k4_xboole_0(A_195,k1_xboole_0) = A_195 ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_91])).

tff(c_1196,plain,(
    ! [A_195] : k4_xboole_0(A_195,'#skF_4') = A_195 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_918])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_936,plain,(
    ! [C_196,D_197,A_198,B_199] :
      ( ~ r1_xboole_0(C_196,D_197)
      | ~ m2_orders_2(D_197,A_198,B_199)
      | ~ m2_orders_2(C_196,A_198,B_199)
      | ~ m1_orders_1(B_199,k1_orders_1(u1_struct_0(A_198)))
      | ~ l1_orders_2(A_198)
      | ~ v5_orders_2(A_198)
      | ~ v4_orders_2(A_198)
      | ~ v3_orders_2(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1515,plain,(
    ! [B_231,A_232,B_233,A_234] :
      ( ~ m2_orders_2(B_231,A_232,B_233)
      | ~ m2_orders_2(A_234,A_232,B_233)
      | ~ m1_orders_1(B_233,k1_orders_1(u1_struct_0(A_232)))
      | ~ l1_orders_2(A_232)
      | ~ v5_orders_2(A_232)
      | ~ v4_orders_2(A_232)
      | ~ v3_orders_2(A_232)
      | v2_struct_0(A_232)
      | k4_xboole_0(A_234,B_231) != A_234 ) ),
    inference(resolution,[status(thm)],[c_28,c_936])).

tff(c_1517,plain,(
    ! [A_234] :
      ( ~ m2_orders_2(A_234,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_234,'#skF_4') != A_234 ) ),
    inference(resolution,[status(thm)],[c_46,c_1515])).

tff(c_1520,plain,(
    ! [A_234] :
      ( ~ m2_orders_2(A_234,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_58,c_56,c_54,c_52,c_50,c_1517])).

tff(c_1521,plain,(
    ! [A_234] : ~ m2_orders_2(A_234,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1520])).

tff(c_1523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1521,c_46])).

tff(c_1525,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1529,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1525,c_6])).

tff(c_1539,plain,(
    ! [B_237,A_238] :
      ( B_237 = A_238
      | ~ r1_tarski(B_237,A_238)
      | ~ r1_tarski(A_238,B_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1546,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1529,c_1539])).

tff(c_1552,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1546])).

tff(c_48,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_2095,plain,(
    ! [C_289,A_290,B_291] :
      ( m1_subset_1(C_289,k1_zfmisc_1(u1_struct_0(A_290)))
      | ~ m2_orders_2(C_289,A_290,B_291)
      | ~ m1_orders_1(B_291,k1_orders_1(u1_struct_0(A_290)))
      | ~ l1_orders_2(A_290)
      | ~ v5_orders_2(A_290)
      | ~ v4_orders_2(A_290)
      | ~ v3_orders_2(A_290)
      | v2_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2099,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2095])).

tff(c_2106,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_2099])).

tff(c_2107,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2106])).

tff(c_16,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1524,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2581,plain,(
    ! [C_311,A_312,D_313,B_314] :
      ( m1_orders_2(C_311,A_312,D_313)
      | m1_orders_2(D_313,A_312,C_311)
      | D_313 = C_311
      | ~ m2_orders_2(D_313,A_312,B_314)
      | ~ m2_orders_2(C_311,A_312,B_314)
      | ~ m1_orders_1(B_314,k1_orders_1(u1_struct_0(A_312)))
      | ~ l1_orders_2(A_312)
      | ~ v5_orders_2(A_312)
      | ~ v4_orders_2(A_312)
      | ~ v3_orders_2(A_312)
      | v2_struct_0(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_2585,plain,(
    ! [C_311] :
      ( m1_orders_2(C_311,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_311)
      | C_311 = '#skF_3'
      | ~ m2_orders_2(C_311,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_2581])).

tff(c_2592,plain,(
    ! [C_311] :
      ( m1_orders_2(C_311,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_311)
      | C_311 = '#skF_3'
      | ~ m2_orders_2(C_311,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_2585])).

tff(c_2633,plain,(
    ! [C_319] :
      ( m1_orders_2(C_319,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_319)
      | C_319 = '#skF_3'
      | ~ m2_orders_2(C_319,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2592])).

tff(c_2636,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_2633])).

tff(c_2642,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1524,c_2636])).

tff(c_2661,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2642])).

tff(c_2666,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_1552])).

tff(c_2675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2666])).

tff(c_2676,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2642])).

tff(c_36,plain,(
    ! [C_34,B_32,A_28] :
      ( r1_tarski(C_34,B_32)
      | ~ m1_orders_2(C_34,A_28,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_orders_2(A_28)
      | ~ v5_orders_2(A_28)
      | ~ v4_orders_2(A_28)
      | ~ v3_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2685,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2676,c_36])).

tff(c_2700,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2107,c_2685])).

tff(c_2702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1552,c_2700])).

tff(c_2703,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1546])).

tff(c_2707,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2703,c_1525])).

tff(c_2711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_2707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.68  
% 4.04/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.69  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.04/1.69  
% 4.04/1.69  %Foreground sorts:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Background operators:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Foreground operators:
% 4.04/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.04/1.69  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.69  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 4.04/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.69  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 4.04/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.04/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.04/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.04/1.69  tff('#skF_1', type, '#skF_1': $i).
% 4.04/1.69  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.04/1.69  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.04/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.04/1.69  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.04/1.69  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.04/1.69  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.69  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 4.04/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.69  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 4.04/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.04/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.04/1.69  
% 4.04/1.71  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 4.04/1.71  tff(f_221, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 4.04/1.71  tff(f_101, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 4.04/1.71  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.04/1.71  tff(f_120, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 4.04/1.71  tff(f_145, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 4.04/1.71  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.04/1.71  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.04/1.71  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.04/1.71  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.04/1.71  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.04/1.71  tff(f_168, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 4.04/1.71  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.04/1.71  tff(f_196, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 4.04/1.71  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.04/1.71  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_58, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_56, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_54, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_52, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_50, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_46, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_794, plain, (![C_185, A_186, B_187]: (m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0(A_186))) | ~m2_orders_2(C_185, A_186, B_187) | ~m1_orders_1(B_187, k1_orders_1(u1_struct_0(A_186))) | ~l1_orders_2(A_186) | ~v5_orders_2(A_186) | ~v4_orders_2(A_186) | ~v3_orders_2(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.04/1.71  tff(c_796, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_794])).
% 4.04/1.71  tff(c_799, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_796])).
% 4.04/1.71  tff(c_800, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_799])).
% 4.04/1.71  tff(c_142, plain, (![A_105, B_106]: (r2_xboole_0(A_105, B_106) | B_106=A_105 | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.71  tff(c_62, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_132, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 4.04/1.71  tff(c_153, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_142, c_132])).
% 4.04/1.71  tff(c_159, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_153])).
% 4.04/1.71  tff(c_68, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_133, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_132, c_68])).
% 4.04/1.71  tff(c_374, plain, (![C_134, B_135, A_136]: (r1_tarski(C_134, B_135) | ~m1_orders_2(C_134, A_136, B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.04/1.71  tff(c_376, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_133, c_374])).
% 4.04/1.71  tff(c_379, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_376])).
% 4.04/1.71  tff(c_380, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_159, c_379])).
% 4.04/1.71  tff(c_400, plain, (![C_140, A_141, B_142]: (m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~m2_orders_2(C_140, A_141, B_142) | ~m1_orders_1(B_142, k1_orders_1(u1_struct_0(A_141))) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.04/1.71  tff(c_402, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_400])).
% 4.04/1.71  tff(c_407, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_402])).
% 4.04/1.71  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_380, c_407])).
% 4.04/1.71  tff(c_410, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_153])).
% 4.04/1.71  tff(c_412, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_133])).
% 4.04/1.71  tff(c_1023, plain, (![C_203, A_204, B_205]: (~m1_orders_2(C_203, A_204, B_205) | ~m1_orders_2(B_205, A_204, C_203) | k1_xboole_0=B_205 | ~m1_subset_1(C_203, k1_zfmisc_1(u1_struct_0(A_204))) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_orders_2(A_204) | ~v5_orders_2(A_204) | ~v4_orders_2(A_204) | ~v3_orders_2(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.04/1.71  tff(c_1025, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_412, c_1023])).
% 4.04/1.71  tff(c_1028, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_800, c_412, c_1025])).
% 4.04/1.71  tff(c_1029, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_60, c_1028])).
% 4.04/1.71  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.04/1.71  tff(c_24, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.04/1.71  tff(c_75, plain, (![B_91, A_92]: (r1_xboole_0(B_91, A_92) | ~r1_xboole_0(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.04/1.71  tff(c_78, plain, (![B_17, A_16]: (r1_xboole_0(B_17, k4_xboole_0(A_16, B_17)))), inference(resolution, [status(thm)], [c_24, c_75])).
% 4.04/1.71  tff(c_84, plain, (![A_95, B_96]: (k4_xboole_0(A_95, B_96)=A_95 | ~r1_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.04/1.71  tff(c_91, plain, (![B_17, A_16]: (k4_xboole_0(B_17, k4_xboole_0(A_16, B_17))=B_17)), inference(resolution, [status(thm)], [c_78, c_84])).
% 4.04/1.71  tff(c_128, plain, (![A_101, B_102]: (k1_xboole_0=A_101 | ~r1_tarski(A_101, k4_xboole_0(B_102, A_101)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.04/1.71  tff(c_839, plain, (![A_193, B_194]: (k4_xboole_0(A_193, B_194)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_193, B_194), B_194))), inference(superposition, [status(thm), theory('equality')], [c_91, c_128])).
% 4.04/1.71  tff(c_857, plain, (![A_195]: (k4_xboole_0(A_195, A_195)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_839])).
% 4.04/1.71  tff(c_918, plain, (![A_195]: (k4_xboole_0(A_195, k1_xboole_0)=A_195)), inference(superposition, [status(thm), theory('equality')], [c_857, c_91])).
% 4.04/1.71  tff(c_1196, plain, (![A_195]: (k4_xboole_0(A_195, '#skF_4')=A_195)), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_918])).
% 4.04/1.71  tff(c_28, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.04/1.71  tff(c_936, plain, (![C_196, D_197, A_198, B_199]: (~r1_xboole_0(C_196, D_197) | ~m2_orders_2(D_197, A_198, B_199) | ~m2_orders_2(C_196, A_198, B_199) | ~m1_orders_1(B_199, k1_orders_1(u1_struct_0(A_198))) | ~l1_orders_2(A_198) | ~v5_orders_2(A_198) | ~v4_orders_2(A_198) | ~v3_orders_2(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.04/1.71  tff(c_1515, plain, (![B_231, A_232, B_233, A_234]: (~m2_orders_2(B_231, A_232, B_233) | ~m2_orders_2(A_234, A_232, B_233) | ~m1_orders_1(B_233, k1_orders_1(u1_struct_0(A_232))) | ~l1_orders_2(A_232) | ~v5_orders_2(A_232) | ~v4_orders_2(A_232) | ~v3_orders_2(A_232) | v2_struct_0(A_232) | k4_xboole_0(A_234, B_231)!=A_234)), inference(resolution, [status(thm)], [c_28, c_936])).
% 4.04/1.71  tff(c_1517, plain, (![A_234]: (~m2_orders_2(A_234, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | k4_xboole_0(A_234, '#skF_4')!=A_234)), inference(resolution, [status(thm)], [c_46, c_1515])).
% 4.04/1.71  tff(c_1520, plain, (![A_234]: (~m2_orders_2(A_234, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_58, c_56, c_54, c_52, c_50, c_1517])).
% 4.04/1.71  tff(c_1521, plain, (![A_234]: (~m2_orders_2(A_234, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_1520])).
% 4.04/1.71  tff(c_1523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1521, c_46])).
% 4.04/1.71  tff(c_1525, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 4.04/1.71  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.71  tff(c_1529, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1525, c_6])).
% 4.04/1.71  tff(c_1539, plain, (![B_237, A_238]: (B_237=A_238 | ~r1_tarski(B_237, A_238) | ~r1_tarski(A_238, B_237))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.04/1.71  tff(c_1546, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1529, c_1539])).
% 4.04/1.71  tff(c_1552, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1546])).
% 4.04/1.71  tff(c_48, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.04/1.71  tff(c_2095, plain, (![C_289, A_290, B_291]: (m1_subset_1(C_289, k1_zfmisc_1(u1_struct_0(A_290))) | ~m2_orders_2(C_289, A_290, B_291) | ~m1_orders_1(B_291, k1_orders_1(u1_struct_0(A_290))) | ~l1_orders_2(A_290) | ~v5_orders_2(A_290) | ~v4_orders_2(A_290) | ~v3_orders_2(A_290) | v2_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.04/1.71  tff(c_2099, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2095])).
% 4.04/1.71  tff(c_2106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_2099])).
% 4.04/1.71  tff(c_2107, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_2106])).
% 4.04/1.71  tff(c_16, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.04/1.71  tff(c_1524, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 4.04/1.71  tff(c_2581, plain, (![C_311, A_312, D_313, B_314]: (m1_orders_2(C_311, A_312, D_313) | m1_orders_2(D_313, A_312, C_311) | D_313=C_311 | ~m2_orders_2(D_313, A_312, B_314) | ~m2_orders_2(C_311, A_312, B_314) | ~m1_orders_1(B_314, k1_orders_1(u1_struct_0(A_312))) | ~l1_orders_2(A_312) | ~v5_orders_2(A_312) | ~v4_orders_2(A_312) | ~v3_orders_2(A_312) | v2_struct_0(A_312))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.04/1.71  tff(c_2585, plain, (![C_311]: (m1_orders_2(C_311, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_311) | C_311='#skF_3' | ~m2_orders_2(C_311, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_2581])).
% 4.04/1.71  tff(c_2592, plain, (![C_311]: (m1_orders_2(C_311, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_311) | C_311='#skF_3' | ~m2_orders_2(C_311, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_2585])).
% 4.04/1.71  tff(c_2633, plain, (![C_319]: (m1_orders_2(C_319, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_319) | C_319='#skF_3' | ~m2_orders_2(C_319, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_2592])).
% 4.04/1.71  tff(c_2636, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_46, c_2633])).
% 4.04/1.71  tff(c_2642, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1524, c_2636])).
% 4.04/1.71  tff(c_2661, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_2642])).
% 4.04/1.71  tff(c_2666, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_1552])).
% 4.04/1.71  tff(c_2675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_2666])).
% 4.04/1.71  tff(c_2676, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_2642])).
% 4.04/1.71  tff(c_36, plain, (![C_34, B_32, A_28]: (r1_tarski(C_34, B_32) | ~m1_orders_2(C_34, A_28, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_orders_2(A_28) | ~v5_orders_2(A_28) | ~v4_orders_2(A_28) | ~v3_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.04/1.71  tff(c_2685, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2676, c_36])).
% 4.04/1.71  tff(c_2700, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2107, c_2685])).
% 4.04/1.71  tff(c_2702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1552, c_2700])).
% 4.04/1.71  tff(c_2703, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1546])).
% 4.04/1.71  tff(c_2707, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2703, c_1525])).
% 4.04/1.71  tff(c_2711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_2707])).
% 4.04/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.71  
% 4.04/1.71  Inference rules
% 4.04/1.71  ----------------------
% 4.04/1.71  #Ref     : 0
% 4.04/1.71  #Sup     : 627
% 4.04/1.71  #Fact    : 0
% 4.04/1.71  #Define  : 0
% 4.04/1.71  #Split   : 5
% 4.04/1.71  #Chain   : 0
% 4.04/1.71  #Close   : 0
% 4.04/1.71  
% 4.04/1.71  Ordering : KBO
% 4.04/1.71  
% 4.04/1.71  Simplification rules
% 4.04/1.71  ----------------------
% 4.04/1.71  #Subsume      : 53
% 4.04/1.71  #Demod        : 515
% 4.04/1.71  #Tautology    : 370
% 4.04/1.71  #SimpNegUnit  : 27
% 4.04/1.71  #BackRed      : 23
% 4.04/1.71  
% 4.04/1.71  #Partial instantiations: 0
% 4.04/1.71  #Strategies tried      : 1
% 4.04/1.71  
% 4.04/1.71  Timing (in seconds)
% 4.04/1.71  ----------------------
% 4.04/1.71  Preprocessing        : 0.34
% 4.04/1.71  Parsing              : 0.19
% 4.04/1.71  CNF conversion       : 0.03
% 4.04/1.71  Main loop            : 0.59
% 4.04/1.71  Inferencing          : 0.21
% 4.04/1.71  Reduction            : 0.20
% 4.04/1.71  Demodulation         : 0.15
% 4.04/1.71  BG Simplification    : 0.03
% 4.04/1.71  Subsumption          : 0.11
% 4.04/1.71  Abstraction          : 0.03
% 4.04/1.71  MUC search           : 0.00
% 4.04/1.71  Cooper               : 0.00
% 4.04/1.71  Total                : 0.98
% 4.04/1.71  Index Insertion      : 0.00
% 4.04/1.71  Index Deletion       : 0.00
% 4.04/1.71  Index Matching       : 0.00
% 4.04/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
