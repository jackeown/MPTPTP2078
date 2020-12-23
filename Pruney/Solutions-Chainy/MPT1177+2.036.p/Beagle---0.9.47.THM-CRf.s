%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:00 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 295 expanded)
%              Number of leaves         :   37 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  303 (1260 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

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

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(f_56,axiom,(
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

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_52,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_50,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_48,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_46,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_44,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_42,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_265,plain,(
    ! [C_133,A_134,B_135] :
      ( m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m2_orders_2(C_133,A_134,B_135)
      | ~ m1_orders_1(B_135,k1_orders_1(u1_struct_0(A_134)))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_267,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_265])).

tff(c_270,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_267])).

tff(c_271,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_270])).

tff(c_104,plain,(
    ! [A_90,B_91] :
      ( r2_xboole_0(A_90,B_91)
      | B_91 = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_69,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_115,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_69])).

tff(c_121,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_70,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_62])).

tff(c_187,plain,(
    ! [C_110,B_111,A_112] :
      ( r1_tarski(C_110,B_111)
      | ~ m1_orders_2(C_110,A_112,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_189,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_187])).

tff(c_192,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_189])).

tff(c_193,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_121,c_192])).

tff(c_40,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_194,plain,(
    ! [C_113,A_114,B_115] :
      ( m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m2_orders_2(C_113,A_114,B_115)
      | ~ m1_orders_1(B_115,k1_orders_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_198,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_194])).

tff(c_205,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_198])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_193,c_205])).

tff(c_208,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_210,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_70])).

tff(c_286,plain,(
    ! [C_143,A_144,B_145] :
      ( ~ m1_orders_2(C_143,A_144,B_145)
      | ~ m1_orders_2(B_145,A_144,C_143)
      | k1_xboole_0 = B_145
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_orders_2(A_144)
      | ~ v5_orders_2(A_144)
      | ~ v4_orders_2(A_144)
      | ~ v3_orders_2(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_288,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_210,c_286])).

tff(c_291,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_271,c_210,c_288])).

tff(c_292,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_291])).

tff(c_20,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_xboole_0(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_219,plain,(
    ! [A_116,B_117] :
      ( ~ r1_tarski(A_116,'#skF_1'(A_116,B_117))
      | r1_xboole_0(A_116,B_117) ) ),
    inference(resolution,[status(thm)],[c_94,c_22])).

tff(c_224,plain,(
    ! [B_117] : r1_xboole_0(k1_xboole_0,B_117) ),
    inference(resolution,[status(thm)],[c_20,c_219])).

tff(c_279,plain,(
    ! [C_139,D_140,A_141,B_142] :
      ( ~ r1_xboole_0(C_139,D_140)
      | ~ m2_orders_2(D_140,A_141,B_142)
      | ~ m2_orders_2(C_139,A_141,B_142)
      | ~ m1_orders_1(B_142,k1_orders_1(u1_struct_0(A_141)))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_285,plain,(
    ! [B_117,A_141,B_142] :
      ( ~ m2_orders_2(B_117,A_141,B_142)
      | ~ m2_orders_2(k1_xboole_0,A_141,B_142)
      | ~ m1_orders_1(B_142,k1_orders_1(u1_struct_0(A_141)))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_224,c_279])).

tff(c_380,plain,(
    ! [B_161,A_162,B_163] :
      ( ~ m2_orders_2(B_161,A_162,B_163)
      | ~ m2_orders_2('#skF_4',A_162,B_163)
      | ~ m1_orders_1(B_163,k1_orders_1(u1_struct_0(A_162)))
      | ~ l1_orders_2(A_162)
      | ~ v5_orders_2(A_162)
      | ~ v4_orders_2(A_162)
      | ~ v3_orders_2(A_162)
      | v2_struct_0(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_285])).

tff(c_382,plain,
    ( ~ m2_orders_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_380])).

tff(c_385,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_42,c_382])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_385])).

tff(c_389,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_401,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_389,c_6])).

tff(c_408,plain,(
    ! [B_166,A_167] :
      ( B_166 = A_167
      | ~ r1_tarski(B_166,A_167)
      | ~ r1_tarski(A_167,B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_415,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_401,c_408])).

tff(c_434,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_519,plain,(
    ! [C_194,A_195,B_196] :
      ( m1_subset_1(C_194,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m2_orders_2(C_194,A_195,B_196)
      | ~ m1_orders_1(B_196,k1_orders_1(u1_struct_0(A_195)))
      | ~ l1_orders_2(A_195)
      | ~ v5_orders_2(A_195)
      | ~ v4_orders_2(A_195)
      | ~ v3_orders_2(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_521,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_519])).

tff(c_526,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_521])).

tff(c_527,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_526])).

tff(c_18,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_388,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_555,plain,(
    ! [C_214,A_215,D_216,B_217] :
      ( m1_orders_2(C_214,A_215,D_216)
      | m1_orders_2(D_216,A_215,C_214)
      | D_216 = C_214
      | ~ m2_orders_2(D_216,A_215,B_217)
      | ~ m2_orders_2(C_214,A_215,B_217)
      | ~ m1_orders_1(B_217,k1_orders_1(u1_struct_0(A_215)))
      | ~ l1_orders_2(A_215)
      | ~ v5_orders_2(A_215)
      | ~ v4_orders_2(A_215)
      | ~ v3_orders_2(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_557,plain,(
    ! [C_214] :
      ( m1_orders_2(C_214,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_214)
      | C_214 = '#skF_4'
      | ~ m2_orders_2(C_214,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_555])).

tff(c_562,plain,(
    ! [C_214] :
      ( m1_orders_2(C_214,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_214)
      | C_214 = '#skF_4'
      | ~ m2_orders_2(C_214,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_557])).

tff(c_568,plain,(
    ! [C_218] :
      ( m1_orders_2(C_218,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_218)
      | C_218 = '#skF_4'
      | ~ m2_orders_2(C_218,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_562])).

tff(c_574,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_568])).

tff(c_579,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_574])).

tff(c_580,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_583,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_434])).

tff(c_592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_583])).

tff(c_593,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_30,plain,(
    ! [C_27,B_25,A_21] :
      ( r1_tarski(C_27,B_25)
      | ~ m1_orders_2(C_27,A_21,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_orders_2(A_21)
      | ~ v5_orders_2(A_21)
      | ~ v4_orders_2(A_21)
      | ~ v3_orders_2(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_614,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_593,c_30])).

tff(c_629,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_527,c_614])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_434,c_629])).

tff(c_632,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_636,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_389])).

tff(c_640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:33:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.41  
% 2.83/1.41  %Foreground sorts:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Background operators:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Foreground operators:
% 2.83/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.41  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.83/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.41  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.83/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.83/1.41  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.83/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.83/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.83/1.41  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.41  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.83/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.41  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.83/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.41  
% 2.83/1.43  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.83/1.43  tff(f_221, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.83/1.43  tff(f_101, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.83/1.43  tff(f_120, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.83/1.43  tff(f_145, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.83/1.43  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.83/1.43  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.83/1.43  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.83/1.43  tff(f_168, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.83/1.43  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.83/1.43  tff(f_196, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.83/1.43  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.43  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_52, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_50, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_48, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_46, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_44, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_42, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_265, plain, (![C_133, A_134, B_135]: (m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~m2_orders_2(C_133, A_134, B_135) | ~m1_orders_1(B_135, k1_orders_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.83/1.43  tff(c_267, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_265])).
% 2.83/1.43  tff(c_270, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_267])).
% 2.83/1.43  tff(c_271, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_270])).
% 2.83/1.43  tff(c_104, plain, (![A_90, B_91]: (r2_xboole_0(A_90, B_91) | B_91=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.43  tff(c_56, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_69, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 2.83/1.43  tff(c_115, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_104, c_69])).
% 2.83/1.43  tff(c_121, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_115])).
% 2.83/1.43  tff(c_62, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_70, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_69, c_62])).
% 2.83/1.43  tff(c_187, plain, (![C_110, B_111, A_112]: (r1_tarski(C_110, B_111) | ~m1_orders_2(C_110, A_112, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.83/1.43  tff(c_189, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_187])).
% 2.83/1.43  tff(c_192, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_189])).
% 2.83/1.43  tff(c_193, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_121, c_192])).
% 2.83/1.43  tff(c_40, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.83/1.43  tff(c_194, plain, (![C_113, A_114, B_115]: (m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~m2_orders_2(C_113, A_114, B_115) | ~m1_orders_1(B_115, k1_orders_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.83/1.43  tff(c_198, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_194])).
% 2.83/1.43  tff(c_205, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_198])).
% 2.83/1.43  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_193, c_205])).
% 2.83/1.43  tff(c_208, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_115])).
% 2.83/1.43  tff(c_210, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_70])).
% 2.83/1.43  tff(c_286, plain, (![C_143, A_144, B_145]: (~m1_orders_2(C_143, A_144, B_145) | ~m1_orders_2(B_145, A_144, C_143) | k1_xboole_0=B_145 | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(A_144))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_orders_2(A_144) | ~v5_orders_2(A_144) | ~v4_orders_2(A_144) | ~v3_orders_2(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.83/1.43  tff(c_288, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_210, c_286])).
% 2.83/1.43  tff(c_291, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_271, c_210, c_288])).
% 2.83/1.43  tff(c_292, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_291])).
% 2.83/1.43  tff(c_20, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.43  tff(c_94, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), A_86) | r1_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.43  tff(c_22, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.83/1.43  tff(c_219, plain, (![A_116, B_117]: (~r1_tarski(A_116, '#skF_1'(A_116, B_117)) | r1_xboole_0(A_116, B_117))), inference(resolution, [status(thm)], [c_94, c_22])).
% 2.83/1.43  tff(c_224, plain, (![B_117]: (r1_xboole_0(k1_xboole_0, B_117))), inference(resolution, [status(thm)], [c_20, c_219])).
% 2.83/1.43  tff(c_279, plain, (![C_139, D_140, A_141, B_142]: (~r1_xboole_0(C_139, D_140) | ~m2_orders_2(D_140, A_141, B_142) | ~m2_orders_2(C_139, A_141, B_142) | ~m1_orders_1(B_142, k1_orders_1(u1_struct_0(A_141))) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.83/1.43  tff(c_285, plain, (![B_117, A_141, B_142]: (~m2_orders_2(B_117, A_141, B_142) | ~m2_orders_2(k1_xboole_0, A_141, B_142) | ~m1_orders_1(B_142, k1_orders_1(u1_struct_0(A_141))) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_224, c_279])).
% 2.83/1.43  tff(c_380, plain, (![B_161, A_162, B_163]: (~m2_orders_2(B_161, A_162, B_163) | ~m2_orders_2('#skF_4', A_162, B_163) | ~m1_orders_1(B_163, k1_orders_1(u1_struct_0(A_162))) | ~l1_orders_2(A_162) | ~v5_orders_2(A_162) | ~v4_orders_2(A_162) | ~v3_orders_2(A_162) | v2_struct_0(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_285])).
% 2.83/1.43  tff(c_382, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_380])).
% 2.83/1.43  tff(c_385, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_42, c_382])).
% 2.83/1.43  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_385])).
% 2.83/1.43  tff(c_389, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 2.83/1.43  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.43  tff(c_401, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_389, c_6])).
% 2.83/1.43  tff(c_408, plain, (![B_166, A_167]: (B_166=A_167 | ~r1_tarski(B_166, A_167) | ~r1_tarski(A_167, B_166))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.83/1.43  tff(c_415, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_401, c_408])).
% 2.83/1.43  tff(c_434, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_415])).
% 2.83/1.43  tff(c_519, plain, (![C_194, A_195, B_196]: (m1_subset_1(C_194, k1_zfmisc_1(u1_struct_0(A_195))) | ~m2_orders_2(C_194, A_195, B_196) | ~m1_orders_1(B_196, k1_orders_1(u1_struct_0(A_195))) | ~l1_orders_2(A_195) | ~v5_orders_2(A_195) | ~v4_orders_2(A_195) | ~v3_orders_2(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.83/1.43  tff(c_521, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_519])).
% 2.83/1.43  tff(c_526, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_521])).
% 2.83/1.43  tff(c_527, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_526])).
% 2.83/1.43  tff(c_18, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.83/1.43  tff(c_388, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 2.83/1.43  tff(c_555, plain, (![C_214, A_215, D_216, B_217]: (m1_orders_2(C_214, A_215, D_216) | m1_orders_2(D_216, A_215, C_214) | D_216=C_214 | ~m2_orders_2(D_216, A_215, B_217) | ~m2_orders_2(C_214, A_215, B_217) | ~m1_orders_1(B_217, k1_orders_1(u1_struct_0(A_215))) | ~l1_orders_2(A_215) | ~v5_orders_2(A_215) | ~v4_orders_2(A_215) | ~v3_orders_2(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_196])).
% 2.83/1.43  tff(c_557, plain, (![C_214]: (m1_orders_2(C_214, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_214) | C_214='#skF_4' | ~m2_orders_2(C_214, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_555])).
% 2.83/1.43  tff(c_562, plain, (![C_214]: (m1_orders_2(C_214, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_214) | C_214='#skF_4' | ~m2_orders_2(C_214, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_557])).
% 2.83/1.43  tff(c_568, plain, (![C_218]: (m1_orders_2(C_218, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_218) | C_218='#skF_4' | ~m2_orders_2(C_218, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_562])).
% 2.83/1.43  tff(c_574, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_568])).
% 2.83/1.43  tff(c_579, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_388, c_574])).
% 2.83/1.43  tff(c_580, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_579])).
% 2.83/1.43  tff(c_583, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_434])).
% 2.83/1.43  tff(c_592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_583])).
% 2.83/1.43  tff(c_593, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_579])).
% 2.83/1.43  tff(c_30, plain, (![C_27, B_25, A_21]: (r1_tarski(C_27, B_25) | ~m1_orders_2(C_27, A_21, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_orders_2(A_21) | ~v5_orders_2(A_21) | ~v4_orders_2(A_21) | ~v3_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.83/1.43  tff(c_614, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_593, c_30])).
% 2.83/1.43  tff(c_629, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_527, c_614])).
% 2.83/1.43  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_434, c_629])).
% 2.83/1.43  tff(c_632, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_415])).
% 2.83/1.43  tff(c_636, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_389])).
% 2.83/1.43  tff(c_640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_636])).
% 2.83/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  Inference rules
% 2.83/1.43  ----------------------
% 2.83/1.43  #Ref     : 0
% 2.83/1.43  #Sup     : 95
% 2.83/1.43  #Fact    : 0
% 2.83/1.43  #Define  : 0
% 2.83/1.43  #Split   : 5
% 2.83/1.43  #Chain   : 0
% 2.83/1.43  #Close   : 0
% 2.83/1.43  
% 2.83/1.43  Ordering : KBO
% 2.83/1.43  
% 2.83/1.43  Simplification rules
% 2.83/1.43  ----------------------
% 2.83/1.43  #Subsume      : 14
% 2.83/1.43  #Demod        : 178
% 2.83/1.43  #Tautology    : 46
% 2.83/1.43  #SimpNegUnit  : 30
% 2.83/1.43  #BackRed      : 20
% 2.83/1.43  
% 2.83/1.43  #Partial instantiations: 0
% 2.83/1.43  #Strategies tried      : 1
% 2.83/1.43  
% 2.83/1.43  Timing (in seconds)
% 2.83/1.43  ----------------------
% 2.83/1.43  Preprocessing        : 0.33
% 2.83/1.43  Parsing              : 0.18
% 2.83/1.43  CNF conversion       : 0.03
% 2.83/1.43  Main loop            : 0.32
% 2.83/1.43  Inferencing          : 0.12
% 2.83/1.43  Reduction            : 0.10
% 2.83/1.43  Demodulation         : 0.07
% 2.83/1.43  BG Simplification    : 0.02
% 2.83/1.43  Subsumption          : 0.06
% 2.83/1.43  Abstraction          : 0.01
% 2.83/1.43  MUC search           : 0.00
% 2.83/1.43  Cooper               : 0.00
% 2.83/1.43  Total                : 0.69
% 2.83/1.43  Index Insertion      : 0.00
% 2.83/1.43  Index Deletion       : 0.00
% 2.83/1.43  Index Matching       : 0.00
% 2.83/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
