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
% DateTime   : Thu Dec  3 10:19:57 EST 2020

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 303 expanded)
%              Number of leaves         :   36 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  302 (1271 expanded)
%              Number of equality atoms :   27 (  57 expanded)
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

tff(f_209,negated_conjecture,(
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

tff(f_89,axiom,(
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

tff(f_108,axiom,(
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

tff(f_133,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_156,axiom,(
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

tff(f_184,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_52,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_50,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_44,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_1240,plain,(
    ! [C_192,A_193,B_194] :
      ( m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ m2_orders_2(C_192,A_193,B_194)
      | ~ m1_orders_1(B_194,k1_orders_1(u1_struct_0(A_193)))
      | ~ l1_orders_2(A_193)
      | ~ v5_orders_2(A_193)
      | ~ v4_orders_2(A_193)
      | ~ v3_orders_2(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1242,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1240])).

tff(c_1245,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_1242])).

tff(c_1246,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1245])).

tff(c_104,plain,(
    ! [A_89,B_90] :
      ( r2_xboole_0(A_89,B_90)
      | B_90 = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_79,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_115,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_79])).

tff(c_122,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_85,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_62])).

tff(c_343,plain,(
    ! [C_112,B_113,A_114] :
      ( r1_tarski(C_112,B_113)
      | ~ m1_orders_2(C_112,A_114,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_345,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_343])).

tff(c_348,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_345])).

tff(c_349,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_122,c_348])).

tff(c_825,plain,(
    ! [C_153,A_154,B_155] :
      ( m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m2_orders_2(C_153,A_154,B_155)
      | ~ m1_orders_1(B_155,k1_orders_1(u1_struct_0(A_154)))
      | ~ l1_orders_2(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v4_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_829,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_825])).

tff(c_836,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_829])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_349,c_836])).

tff(c_839,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_841,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_85])).

tff(c_1611,plain,(
    ! [C_228,A_229,B_230] :
      ( ~ m1_orders_2(C_228,A_229,B_230)
      | ~ m1_orders_2(B_230,A_229,C_228)
      | k1_xboole_0 = B_230
      | ~ m1_subset_1(C_228,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_orders_2(A_229)
      | ~ v5_orders_2(A_229)
      | ~ v4_orders_2(A_229)
      | ~ v3_orders_2(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1613,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_841,c_1611])).

tff(c_1616,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1246,c_841,c_1613])).

tff(c_1617,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1616])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = k1_xboole_0
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_86,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_xboole_0(A_84,C_85)
      | ~ r1_tarski(A_84,k4_xboole_0(B_86,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,(
    ! [B_87,C_88] : r1_xboole_0(k4_xboole_0(B_87,C_88),C_88) ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_103,plain,(
    ! [B_6] : r1_xboole_0(k1_xboole_0,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_100])).

tff(c_1503,plain,(
    ! [C_216,D_217,A_218,B_219] :
      ( ~ r1_xboole_0(C_216,D_217)
      | ~ m2_orders_2(D_217,A_218,B_219)
      | ~ m2_orders_2(C_216,A_218,B_219)
      | ~ m1_orders_1(B_219,k1_orders_1(u1_struct_0(A_218)))
      | ~ l1_orders_2(A_218)
      | ~ v5_orders_2(A_218)
      | ~ v4_orders_2(A_218)
      | ~ v3_orders_2(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1517,plain,(
    ! [B_6,A_218,B_219] :
      ( ~ m2_orders_2(B_6,A_218,B_219)
      | ~ m2_orders_2(k1_xboole_0,A_218,B_219)
      | ~ m1_orders_1(B_219,k1_orders_1(u1_struct_0(A_218)))
      | ~ l1_orders_2(A_218)
      | ~ v5_orders_2(A_218)
      | ~ v4_orders_2(A_218)
      | ~ v3_orders_2(A_218)
      | v2_struct_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_103,c_1503])).

tff(c_5930,plain,(
    ! [B_385,A_386,B_387] :
      ( ~ m2_orders_2(B_385,A_386,B_387)
      | ~ m2_orders_2('#skF_4',A_386,B_387)
      | ~ m1_orders_1(B_387,k1_orders_1(u1_struct_0(A_386)))
      | ~ l1_orders_2(A_386)
      | ~ v5_orders_2(A_386)
      | ~ v4_orders_2(A_386)
      | ~ v3_orders_2(A_386)
      | v2_struct_0(A_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1617,c_1517])).

tff(c_5932,plain,
    ( ~ m2_orders_2('#skF_4','#skF_1','#skF_2')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_5930])).

tff(c_5935,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_40,c_5932])).

tff(c_5937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5935])).

tff(c_5939,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5943,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_5939,c_6])).

tff(c_5984,plain,(
    ! [B_396,A_397] :
      ( B_396 = A_397
      | ~ r1_tarski(B_396,A_397)
      | ~ r1_tarski(A_397,B_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5992,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_5943,c_5984])).

tff(c_5998,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5992])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_6469,plain,(
    ! [C_438,A_439,B_440] :
      ( m1_subset_1(C_438,k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ m2_orders_2(C_438,A_439,B_440)
      | ~ m1_orders_1(B_440,k1_orders_1(u1_struct_0(A_439)))
      | ~ l1_orders_2(A_439)
      | ~ v5_orders_2(A_439)
      | ~ v4_orders_2(A_439)
      | ~ v3_orders_2(A_439)
      | v2_struct_0(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6471,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_6469])).

tff(c_6476,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_6471])).

tff(c_6477,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6476])).

tff(c_5938,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_7293,plain,(
    ! [C_493,A_494,D_495,B_496] :
      ( m1_orders_2(C_493,A_494,D_495)
      | m1_orders_2(D_495,A_494,C_493)
      | D_495 = C_493
      | ~ m2_orders_2(D_495,A_494,B_496)
      | ~ m2_orders_2(C_493,A_494,B_496)
      | ~ m1_orders_1(B_496,k1_orders_1(u1_struct_0(A_494)))
      | ~ l1_orders_2(A_494)
      | ~ v5_orders_2(A_494)
      | ~ v4_orders_2(A_494)
      | ~ v3_orders_2(A_494)
      | v2_struct_0(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_7297,plain,(
    ! [C_493] :
      ( m1_orders_2(C_493,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_493)
      | C_493 = '#skF_4'
      | ~ m2_orders_2(C_493,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_7293])).

tff(c_7304,plain,(
    ! [C_493] :
      ( m1_orders_2(C_493,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_493)
      | C_493 = '#skF_4'
      | ~ m2_orders_2(C_493,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_7297])).

tff(c_7359,plain,(
    ! [C_502] :
      ( m1_orders_2(C_502,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_502)
      | C_502 = '#skF_4'
      | ~ m2_orders_2(C_502,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_7304])).

tff(c_7362,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_7359])).

tff(c_7368,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5938,c_7362])).

tff(c_7371,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7368])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6002,plain,(
    k4_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_5998])).

tff(c_7374,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7371,c_6002])).

tff(c_7385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_7374])).

tff(c_7386,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_7368])).

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
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7407,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7386,c_30])).

tff(c_7422,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_6477,c_7407])).

tff(c_7424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5998,c_7422])).

tff(c_7425,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5992])).

tff(c_7430,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7425,c_5939])).

tff(c_7435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_7430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:03:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.56/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.12  
% 5.56/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.12  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.56/2.12  
% 5.56/2.12  %Foreground sorts:
% 5.56/2.12  
% 5.56/2.12  
% 5.56/2.12  %Background operators:
% 5.56/2.12  
% 5.56/2.12  
% 5.56/2.12  %Foreground operators:
% 5.56/2.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.56/2.12  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.56/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.56/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.56/2.12  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 5.56/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.56/2.12  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 5.56/2.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.56/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.56/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.56/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.56/2.12  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.56/2.12  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.56/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.56/2.12  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.56/2.12  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.56/2.12  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 5.56/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.12  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 5.56/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.56/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.12  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 5.56/2.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.56/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.56/2.12  
% 5.69/2.14  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 5.69/2.14  tff(f_209, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 5.69/2.14  tff(f_89, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 5.69/2.14  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.69/2.14  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 5.69/2.14  tff(f_133, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 5.69/2.14  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.69/2.14  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.69/2.14  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.69/2.14  tff(f_156, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 5.69/2.14  tff(f_184, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 5.69/2.14  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.69/2.14  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_1240, plain, (![C_192, A_193, B_194]: (m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(A_193))) | ~m2_orders_2(C_192, A_193, B_194) | ~m1_orders_1(B_194, k1_orders_1(u1_struct_0(A_193))) | ~l1_orders_2(A_193) | ~v5_orders_2(A_193) | ~v4_orders_2(A_193) | ~v3_orders_2(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.69/2.14  tff(c_1242, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1240])).
% 5.69/2.14  tff(c_1245, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_1242])).
% 5.69/2.14  tff(c_1246, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_1245])).
% 5.69/2.14  tff(c_104, plain, (![A_89, B_90]: (r2_xboole_0(A_89, B_90) | B_90=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.14  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_79, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 5.69/2.14  tff(c_115, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_104, c_79])).
% 5.69/2.14  tff(c_122, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_115])).
% 5.69/2.14  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_85, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_79, c_62])).
% 5.69/2.14  tff(c_343, plain, (![C_112, B_113, A_114]: (r1_tarski(C_112, B_113) | ~m1_orders_2(C_112, A_114, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.69/2.14  tff(c_345, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_85, c_343])).
% 5.69/2.14  tff(c_348, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_345])).
% 5.69/2.14  tff(c_349, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_122, c_348])).
% 5.69/2.14  tff(c_825, plain, (![C_153, A_154, B_155]: (m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~m2_orders_2(C_153, A_154, B_155) | ~m1_orders_1(B_155, k1_orders_1(u1_struct_0(A_154))) | ~l1_orders_2(A_154) | ~v5_orders_2(A_154) | ~v4_orders_2(A_154) | ~v3_orders_2(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.69/2.14  tff(c_829, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_825])).
% 5.69/2.14  tff(c_836, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_829])).
% 5.69/2.14  tff(c_838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_349, c_836])).
% 5.69/2.14  tff(c_839, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_115])).
% 5.69/2.14  tff(c_841, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_85])).
% 5.69/2.14  tff(c_1611, plain, (![C_228, A_229, B_230]: (~m1_orders_2(C_228, A_229, B_230) | ~m1_orders_2(B_230, A_229, C_228) | k1_xboole_0=B_230 | ~m1_subset_1(C_228, k1_zfmisc_1(u1_struct_0(A_229))) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_orders_2(A_229) | ~v5_orders_2(A_229) | ~v4_orders_2(A_229) | ~v3_orders_2(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.69/2.14  tff(c_1613, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_841, c_1611])).
% 5.69/2.14  tff(c_1616, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1246, c_841, c_1613])).
% 5.69/2.14  tff(c_1617, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_1616])).
% 5.69/2.14  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.69/2.14  tff(c_67, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=k1_xboole_0 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.69/2.14  tff(c_71, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_67])).
% 5.69/2.14  tff(c_86, plain, (![A_84, C_85, B_86]: (r1_xboole_0(A_84, C_85) | ~r1_tarski(A_84, k4_xboole_0(B_86, C_85)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.69/2.14  tff(c_100, plain, (![B_87, C_88]: (r1_xboole_0(k4_xboole_0(B_87, C_88), C_88))), inference(resolution, [status(thm)], [c_14, c_86])).
% 5.69/2.14  tff(c_103, plain, (![B_6]: (r1_xboole_0(k1_xboole_0, B_6))), inference(superposition, [status(thm), theory('equality')], [c_71, c_100])).
% 5.69/2.14  tff(c_1503, plain, (![C_216, D_217, A_218, B_219]: (~r1_xboole_0(C_216, D_217) | ~m2_orders_2(D_217, A_218, B_219) | ~m2_orders_2(C_216, A_218, B_219) | ~m1_orders_1(B_219, k1_orders_1(u1_struct_0(A_218))) | ~l1_orders_2(A_218) | ~v5_orders_2(A_218) | ~v4_orders_2(A_218) | ~v3_orders_2(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.69/2.14  tff(c_1517, plain, (![B_6, A_218, B_219]: (~m2_orders_2(B_6, A_218, B_219) | ~m2_orders_2(k1_xboole_0, A_218, B_219) | ~m1_orders_1(B_219, k1_orders_1(u1_struct_0(A_218))) | ~l1_orders_2(A_218) | ~v5_orders_2(A_218) | ~v4_orders_2(A_218) | ~v3_orders_2(A_218) | v2_struct_0(A_218))), inference(resolution, [status(thm)], [c_103, c_1503])).
% 5.69/2.14  tff(c_5930, plain, (![B_385, A_386, B_387]: (~m2_orders_2(B_385, A_386, B_387) | ~m2_orders_2('#skF_4', A_386, B_387) | ~m1_orders_1(B_387, k1_orders_1(u1_struct_0(A_386))) | ~l1_orders_2(A_386) | ~v5_orders_2(A_386) | ~v4_orders_2(A_386) | ~v3_orders_2(A_386) | v2_struct_0(A_386))), inference(demodulation, [status(thm), theory('equality')], [c_1617, c_1517])).
% 5.69/2.14  tff(c_5932, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_5930])).
% 5.69/2.14  tff(c_5935, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_40, c_5932])).
% 5.69/2.14  tff(c_5937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5935])).
% 5.69/2.14  tff(c_5939, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 5.69/2.14  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.14  tff(c_5943, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_5939, c_6])).
% 5.69/2.14  tff(c_5984, plain, (![B_396, A_397]: (B_396=A_397 | ~r1_tarski(B_396, A_397) | ~r1_tarski(A_397, B_396))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.69/2.14  tff(c_5992, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_5943, c_5984])).
% 5.69/2.14  tff(c_5998, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_5992])).
% 5.69/2.14  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.69/2.14  tff(c_6469, plain, (![C_438, A_439, B_440]: (m1_subset_1(C_438, k1_zfmisc_1(u1_struct_0(A_439))) | ~m2_orders_2(C_438, A_439, B_440) | ~m1_orders_1(B_440, k1_orders_1(u1_struct_0(A_439))) | ~l1_orders_2(A_439) | ~v5_orders_2(A_439) | ~v4_orders_2(A_439) | ~v3_orders_2(A_439) | v2_struct_0(A_439))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.69/2.14  tff(c_6471, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_6469])).
% 5.69/2.14  tff(c_6476, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_6471])).
% 5.69/2.14  tff(c_6477, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_6476])).
% 5.69/2.14  tff(c_5938, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 5.69/2.14  tff(c_7293, plain, (![C_493, A_494, D_495, B_496]: (m1_orders_2(C_493, A_494, D_495) | m1_orders_2(D_495, A_494, C_493) | D_495=C_493 | ~m2_orders_2(D_495, A_494, B_496) | ~m2_orders_2(C_493, A_494, B_496) | ~m1_orders_1(B_496, k1_orders_1(u1_struct_0(A_494))) | ~l1_orders_2(A_494) | ~v5_orders_2(A_494) | ~v4_orders_2(A_494) | ~v3_orders_2(A_494) | v2_struct_0(A_494))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.69/2.14  tff(c_7297, plain, (![C_493]: (m1_orders_2(C_493, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_493) | C_493='#skF_4' | ~m2_orders_2(C_493, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_7293])).
% 5.69/2.14  tff(c_7304, plain, (![C_493]: (m1_orders_2(C_493, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_493) | C_493='#skF_4' | ~m2_orders_2(C_493, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_7297])).
% 5.69/2.14  tff(c_7359, plain, (![C_502]: (m1_orders_2(C_502, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_502) | C_502='#skF_4' | ~m2_orders_2(C_502, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_7304])).
% 5.69/2.14  tff(c_7362, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_7359])).
% 5.69/2.14  tff(c_7368, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5938, c_7362])).
% 5.69/2.14  tff(c_7371, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_7368])).
% 5.69/2.14  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.69/2.14  tff(c_6002, plain, (k4_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_5998])).
% 5.69/2.14  tff(c_7374, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7371, c_6002])).
% 5.69/2.14  tff(c_7385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_7374])).
% 5.69/2.14  tff(c_7386, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_7368])).
% 5.69/2.14  tff(c_30, plain, (![C_26, B_24, A_20]: (r1_tarski(C_26, B_24) | ~m1_orders_2(C_26, A_20, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.69/2.14  tff(c_7407, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_7386, c_30])).
% 5.69/2.14  tff(c_7422, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_6477, c_7407])).
% 5.69/2.14  tff(c_7424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5998, c_7422])).
% 5.69/2.14  tff(c_7425, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_5992])).
% 5.69/2.14  tff(c_7430, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7425, c_5939])).
% 5.69/2.14  tff(c_7435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_7430])).
% 5.69/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.14  
% 5.69/2.14  Inference rules
% 5.69/2.14  ----------------------
% 5.69/2.14  #Ref     : 0
% 5.69/2.14  #Sup     : 1758
% 5.69/2.14  #Fact    : 0
% 5.69/2.14  #Define  : 0
% 5.69/2.14  #Split   : 4
% 5.69/2.14  #Chain   : 0
% 5.69/2.14  #Close   : 0
% 5.69/2.14  
% 5.69/2.14  Ordering : KBO
% 5.69/2.14  
% 5.69/2.14  Simplification rules
% 5.69/2.14  ----------------------
% 5.69/2.14  #Subsume      : 458
% 5.69/2.14  #Demod        : 1897
% 5.69/2.14  #Tautology    : 954
% 5.69/2.14  #SimpNegUnit  : 30
% 5.69/2.14  #BackRed      : 39
% 5.69/2.14  
% 5.69/2.14  #Partial instantiations: 0
% 5.69/2.14  #Strategies tried      : 1
% 5.69/2.14  
% 5.69/2.14  Timing (in seconds)
% 5.69/2.14  ----------------------
% 5.69/2.14  Preprocessing        : 0.32
% 5.69/2.14  Parsing              : 0.18
% 5.69/2.14  CNF conversion       : 0.03
% 5.69/2.14  Main loop            : 1.04
% 5.69/2.14  Inferencing          : 0.35
% 5.69/2.14  Reduction            : 0.39
% 5.69/2.14  Demodulation         : 0.30
% 5.69/2.15  BG Simplification    : 0.04
% 5.69/2.15  Subsumption          : 0.20
% 5.69/2.15  Abstraction          : 0.05
% 5.69/2.15  MUC search           : 0.00
% 5.69/2.15  Cooper               : 0.00
% 5.69/2.15  Total                : 1.41
% 5.69/2.15  Index Insertion      : 0.00
% 5.69/2.15  Index Deletion       : 0.00
% 5.69/2.15  Index Matching       : 0.00
% 5.69/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
