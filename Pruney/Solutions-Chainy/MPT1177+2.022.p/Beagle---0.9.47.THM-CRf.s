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
% DateTime   : Thu Dec  3 10:19:58 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 291 expanded)
%              Number of leaves         :   36 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  295 (1249 expanded)
%              Number of equality atoms :   21 (  45 expanded)
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

tff(f_207,negated_conjecture,(
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

tff(f_87,axiom,(
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

tff(f_106,axiom,(
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

tff(f_131,axiom,(
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
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_154,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_182,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_50,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_48,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_46,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_44,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_42,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_446,plain,(
    ! [C_158,A_159,B_160] :
      ( m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m2_orders_2(C_158,A_159,B_160)
      | ~ m1_orders_1(B_160,k1_orders_1(u1_struct_0(A_159)))
      | ~ l1_orders_2(A_159)
      | ~ v5_orders_2(A_159)
      | ~ v4_orders_2(A_159)
      | ~ v3_orders_2(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_448,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_446])).

tff(c_451,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_448])).

tff(c_452,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_451])).

tff(c_81,plain,(
    ! [A_85,B_86] :
      ( r2_xboole_0(A_85,B_86)
      | B_86 = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_66,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_92,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_66])).

tff(c_98,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_60,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_67,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60])).

tff(c_153,plain,(
    ! [C_95,B_96,A_97] :
      ( r1_tarski(C_95,B_96)
      | ~ m1_orders_2(C_95,A_97,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_155,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_67,c_153])).

tff(c_158,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_155])).

tff(c_159,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_98,c_158])).

tff(c_236,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m2_orders_2(C_112,A_113,B_114)
      | ~ m1_orders_1(B_114,k1_orders_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_238,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_236])).

tff(c_243,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_238])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_159,c_243])).

tff(c_246,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_248,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_67])).

tff(c_631,plain,(
    ! [C_235,A_236,B_237] :
      ( ~ m1_orders_2(C_235,A_236,B_237)
      | ~ m1_orders_2(B_237,A_236,C_235)
      | k1_xboole_0 = B_237
      | ~ m1_subset_1(C_235,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_orders_2(A_236)
      | ~ v5_orders_2(A_236)
      | ~ v4_orders_2(A_236)
      | ~ v3_orders_2(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_633,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_248,c_631])).

tff(c_636,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_452,c_248,c_633])).

tff(c_637,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_636])).

tff(c_20,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_xboole_0(A_79,C_80)
      | ~ r1_tarski(A_79,k4_xboole_0(B_81,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    ! [C_80] : r1_xboole_0(k1_xboole_0,C_80) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_566,plain,(
    ! [C_205,D_206,A_207,B_208] :
      ( ~ r1_xboole_0(C_205,D_206)
      | ~ m2_orders_2(D_206,A_207,B_208)
      | ~ m2_orders_2(C_205,A_207,B_208)
      | ~ m1_orders_1(B_208,k1_orders_1(u1_struct_0(A_207)))
      | ~ l1_orders_2(A_207)
      | ~ v5_orders_2(A_207)
      | ~ v4_orders_2(A_207)
      | ~ v3_orders_2(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_590,plain,(
    ! [C_80,A_207,B_208] :
      ( ~ m2_orders_2(C_80,A_207,B_208)
      | ~ m2_orders_2(k1_xboole_0,A_207,B_208)
      | ~ m1_orders_1(B_208,k1_orders_1(u1_struct_0(A_207)))
      | ~ l1_orders_2(A_207)
      | ~ v5_orders_2(A_207)
      | ~ v4_orders_2(A_207)
      | ~ v3_orders_2(A_207)
      | v2_struct_0(A_207) ) ),
    inference(resolution,[status(thm)],[c_78,c_566])).

tff(c_878,plain,(
    ! [C_258,A_259,B_260] :
      ( ~ m2_orders_2(C_258,A_259,B_260)
      | ~ m2_orders_2('#skF_4',A_259,B_260)
      | ~ m1_orders_1(B_260,k1_orders_1(u1_struct_0(A_259)))
      | ~ l1_orders_2(A_259)
      | ~ v5_orders_2(A_259)
      | ~ v4_orders_2(A_259)
      | ~ v3_orders_2(A_259)
      | v2_struct_0(A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_590])).

tff(c_880,plain,
    ( ~ m2_orders_2('#skF_4','#skF_1','#skF_2')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_878])).

tff(c_883,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_38,c_880])).

tff(c_885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_883])).

tff(c_887,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_891,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_887,c_6])).

tff(c_894,plain,(
    ! [B_261,A_262] :
      ( B_261 = A_262
      | ~ r1_tarski(B_261,A_262)
      | ~ r1_tarski(A_262,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_901,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_891,c_894])).

tff(c_920,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_901])).

tff(c_40,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_1184,plain,(
    ! [C_344,A_345,B_346] :
      ( m1_subset_1(C_344,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ m2_orders_2(C_344,A_345,B_346)
      | ~ m1_orders_1(B_346,k1_orders_1(u1_struct_0(A_345)))
      | ~ l1_orders_2(A_345)
      | ~ v5_orders_2(A_345)
      | ~ v4_orders_2(A_345)
      | ~ v3_orders_2(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1188,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1184])).

tff(c_1195,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_1188])).

tff(c_1196,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1195])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_886,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1356,plain,(
    ! [C_420,A_421,D_422,B_423] :
      ( m1_orders_2(C_420,A_421,D_422)
      | m1_orders_2(D_422,A_421,C_420)
      | D_422 = C_420
      | ~ m2_orders_2(D_422,A_421,B_423)
      | ~ m2_orders_2(C_420,A_421,B_423)
      | ~ m1_orders_1(B_423,k1_orders_1(u1_struct_0(A_421)))
      | ~ l1_orders_2(A_421)
      | ~ v5_orders_2(A_421)
      | ~ v4_orders_2(A_421)
      | ~ v3_orders_2(A_421)
      | v2_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1358,plain,(
    ! [C_420] :
      ( m1_orders_2(C_420,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_420)
      | C_420 = '#skF_4'
      | ~ m2_orders_2(C_420,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_1356])).

tff(c_1363,plain,(
    ! [C_420] :
      ( m1_orders_2(C_420,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_420)
      | C_420 = '#skF_4'
      | ~ m2_orders_2(C_420,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_1358])).

tff(c_1369,plain,(
    ! [C_424] :
      ( m1_orders_2(C_424,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_424)
      | C_424 = '#skF_4'
      | ~ m2_orders_2(C_424,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1363])).

tff(c_1375,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_1369])).

tff(c_1380,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_886,c_1375])).

tff(c_1381,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1380])).

tff(c_1384,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_920])).

tff(c_1393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1384])).

tff(c_1394,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1380])).

tff(c_28,plain,(
    ! [C_25,B_23,A_19] :
      ( r1_tarski(C_25,B_23)
      | ~ m1_orders_2(C_25,A_19,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19)
      | ~ v4_orders_2(A_19)
      | ~ v3_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1413,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1394,c_28])).

tff(c_1424,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1196,c_1413])).

tff(c_1426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_920,c_1424])).

tff(c_1427,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_901])).

tff(c_1431,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_887])).

tff(c_1435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_1431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.68  
% 3.76/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.68  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.76/1.68  
% 3.76/1.68  %Foreground sorts:
% 3.76/1.68  
% 3.76/1.68  
% 3.76/1.68  %Background operators:
% 3.76/1.68  
% 3.76/1.68  
% 3.76/1.68  %Foreground operators:
% 3.76/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.76/1.68  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.76/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.76/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.76/1.68  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.76/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.68  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.76/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.76/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.76/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.76/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.76/1.68  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.76/1.68  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.76/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.76/1.68  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.76/1.68  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.76/1.68  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.76/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.68  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.76/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.76/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.68  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.76/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.76/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.76/1.68  
% 3.88/1.70  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 3.88/1.70  tff(f_207, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 3.88/1.70  tff(f_87, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.88/1.70  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.88/1.70  tff(f_106, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 3.88/1.70  tff(f_131, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 3.88/1.70  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.88/1.70  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.88/1.70  tff(f_154, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 3.88/1.70  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/1.70  tff(f_182, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 3.88/1.70  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.70  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_50, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_48, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_46, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_44, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_42, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_446, plain, (![C_158, A_159, B_160]: (m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~m2_orders_2(C_158, A_159, B_160) | ~m1_orders_1(B_160, k1_orders_1(u1_struct_0(A_159))) | ~l1_orders_2(A_159) | ~v5_orders_2(A_159) | ~v4_orders_2(A_159) | ~v3_orders_2(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.88/1.70  tff(c_448, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_446])).
% 3.88/1.70  tff(c_451, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_448])).
% 3.88/1.70  tff(c_452, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_451])).
% 3.88/1.70  tff(c_81, plain, (![A_85, B_86]: (r2_xboole_0(A_85, B_86) | B_86=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.70  tff(c_54, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_66, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 3.88/1.70  tff(c_92, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_81, c_66])).
% 3.88/1.70  tff(c_98, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 3.88/1.70  tff(c_60, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_67, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_60])).
% 3.88/1.70  tff(c_153, plain, (![C_95, B_96, A_97]: (r1_tarski(C_95, B_96) | ~m1_orders_2(C_95, A_97, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.88/1.70  tff(c_155, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_67, c_153])).
% 3.88/1.70  tff(c_158, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_155])).
% 3.88/1.70  tff(c_159, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_98, c_158])).
% 3.88/1.70  tff(c_236, plain, (![C_112, A_113, B_114]: (m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~m2_orders_2(C_112, A_113, B_114) | ~m1_orders_1(B_114, k1_orders_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.88/1.70  tff(c_238, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_236])).
% 3.88/1.70  tff(c_243, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_238])).
% 3.88/1.70  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_159, c_243])).
% 3.88/1.70  tff(c_246, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_92])).
% 3.88/1.70  tff(c_248, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_67])).
% 3.88/1.70  tff(c_631, plain, (![C_235, A_236, B_237]: (~m1_orders_2(C_235, A_236, B_237) | ~m1_orders_2(B_237, A_236, C_235) | k1_xboole_0=B_237 | ~m1_subset_1(C_235, k1_zfmisc_1(u1_struct_0(A_236))) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_orders_2(A_236) | ~v5_orders_2(A_236) | ~v4_orders_2(A_236) | ~v3_orders_2(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.88/1.70  tff(c_633, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_248, c_631])).
% 3.88/1.70  tff(c_636, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_452, c_248, c_633])).
% 3.88/1.70  tff(c_637, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_636])).
% 3.88/1.70  tff(c_20, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.88/1.70  tff(c_68, plain, (![A_79, C_80, B_81]: (r1_xboole_0(A_79, C_80) | ~r1_tarski(A_79, k4_xboole_0(B_81, C_80)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.88/1.70  tff(c_78, plain, (![C_80]: (r1_xboole_0(k1_xboole_0, C_80))), inference(resolution, [status(thm)], [c_20, c_68])).
% 3.88/1.70  tff(c_566, plain, (![C_205, D_206, A_207, B_208]: (~r1_xboole_0(C_205, D_206) | ~m2_orders_2(D_206, A_207, B_208) | ~m2_orders_2(C_205, A_207, B_208) | ~m1_orders_1(B_208, k1_orders_1(u1_struct_0(A_207))) | ~l1_orders_2(A_207) | ~v5_orders_2(A_207) | ~v4_orders_2(A_207) | ~v3_orders_2(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.88/1.70  tff(c_590, plain, (![C_80, A_207, B_208]: (~m2_orders_2(C_80, A_207, B_208) | ~m2_orders_2(k1_xboole_0, A_207, B_208) | ~m1_orders_1(B_208, k1_orders_1(u1_struct_0(A_207))) | ~l1_orders_2(A_207) | ~v5_orders_2(A_207) | ~v4_orders_2(A_207) | ~v3_orders_2(A_207) | v2_struct_0(A_207))), inference(resolution, [status(thm)], [c_78, c_566])).
% 3.88/1.70  tff(c_878, plain, (![C_258, A_259, B_260]: (~m2_orders_2(C_258, A_259, B_260) | ~m2_orders_2('#skF_4', A_259, B_260) | ~m1_orders_1(B_260, k1_orders_1(u1_struct_0(A_259))) | ~l1_orders_2(A_259) | ~v5_orders_2(A_259) | ~v4_orders_2(A_259) | ~v3_orders_2(A_259) | v2_struct_0(A_259))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_590])).
% 3.88/1.70  tff(c_880, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_878])).
% 3.88/1.70  tff(c_883, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_38, c_880])).
% 3.88/1.70  tff(c_885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_883])).
% 3.88/1.70  tff(c_887, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 3.88/1.70  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.70  tff(c_891, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_887, c_6])).
% 3.88/1.70  tff(c_894, plain, (![B_261, A_262]: (B_261=A_262 | ~r1_tarski(B_261, A_262) | ~r1_tarski(A_262, B_261))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.88/1.70  tff(c_901, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_891, c_894])).
% 3.88/1.70  tff(c_920, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_901])).
% 3.88/1.70  tff(c_40, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.88/1.70  tff(c_1184, plain, (![C_344, A_345, B_346]: (m1_subset_1(C_344, k1_zfmisc_1(u1_struct_0(A_345))) | ~m2_orders_2(C_344, A_345, B_346) | ~m1_orders_1(B_346, k1_orders_1(u1_struct_0(A_345))) | ~l1_orders_2(A_345) | ~v5_orders_2(A_345) | ~v4_orders_2(A_345) | ~v3_orders_2(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.88/1.70  tff(c_1188, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1184])).
% 3.88/1.70  tff(c_1195, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_1188])).
% 3.88/1.70  tff(c_1196, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1195])).
% 3.88/1.70  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.88/1.70  tff(c_886, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 3.88/1.70  tff(c_1356, plain, (![C_420, A_421, D_422, B_423]: (m1_orders_2(C_420, A_421, D_422) | m1_orders_2(D_422, A_421, C_420) | D_422=C_420 | ~m2_orders_2(D_422, A_421, B_423) | ~m2_orders_2(C_420, A_421, B_423) | ~m1_orders_1(B_423, k1_orders_1(u1_struct_0(A_421))) | ~l1_orders_2(A_421) | ~v5_orders_2(A_421) | ~v4_orders_2(A_421) | ~v3_orders_2(A_421) | v2_struct_0(A_421))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.88/1.70  tff(c_1358, plain, (![C_420]: (m1_orders_2(C_420, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_420) | C_420='#skF_4' | ~m2_orders_2(C_420, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_1356])).
% 3.88/1.70  tff(c_1363, plain, (![C_420]: (m1_orders_2(C_420, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_420) | C_420='#skF_4' | ~m2_orders_2(C_420, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_1358])).
% 3.88/1.70  tff(c_1369, plain, (![C_424]: (m1_orders_2(C_424, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_424) | C_424='#skF_4' | ~m2_orders_2(C_424, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1363])).
% 3.88/1.70  tff(c_1375, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_1369])).
% 3.88/1.70  tff(c_1380, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_886, c_1375])).
% 3.88/1.70  tff(c_1381, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_1380])).
% 3.88/1.70  tff(c_1384, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_920])).
% 3.88/1.70  tff(c_1393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1384])).
% 3.88/1.70  tff(c_1394, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_1380])).
% 3.88/1.70  tff(c_28, plain, (![C_25, B_23, A_19]: (r1_tarski(C_25, B_23) | ~m1_orders_2(C_25, A_19, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_orders_2(A_19) | ~v5_orders_2(A_19) | ~v4_orders_2(A_19) | ~v3_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.88/1.70  tff(c_1413, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1394, c_28])).
% 3.88/1.70  tff(c_1424, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1196, c_1413])).
% 3.88/1.70  tff(c_1426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_920, c_1424])).
% 3.88/1.70  tff(c_1427, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_901])).
% 3.88/1.70  tff(c_1431, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_887])).
% 3.88/1.70  tff(c_1435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_1431])).
% 3.88/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.70  
% 3.88/1.70  Inference rules
% 3.88/1.70  ----------------------
% 3.88/1.70  #Ref     : 0
% 3.88/1.70  #Sup     : 268
% 3.88/1.70  #Fact    : 0
% 3.88/1.70  #Define  : 0
% 3.88/1.70  #Split   : 4
% 3.88/1.70  #Chain   : 0
% 3.88/1.70  #Close   : 0
% 3.88/1.70  
% 3.88/1.70  Ordering : KBO
% 3.88/1.70  
% 3.88/1.70  Simplification rules
% 3.88/1.70  ----------------------
% 3.88/1.70  #Subsume      : 6
% 3.88/1.70  #Demod        : 541
% 3.88/1.70  #Tautology    : 154
% 3.88/1.70  #SimpNegUnit  : 28
% 3.88/1.70  #BackRed      : 20
% 3.88/1.70  
% 3.88/1.70  #Partial instantiations: 0
% 3.88/1.70  #Strategies tried      : 1
% 3.88/1.70  
% 3.88/1.70  Timing (in seconds)
% 3.88/1.70  ----------------------
% 3.88/1.71  Preprocessing        : 0.37
% 3.88/1.71  Parsing              : 0.20
% 3.88/1.71  CNF conversion       : 0.03
% 3.88/1.71  Main loop            : 0.51
% 3.88/1.71  Inferencing          : 0.19
% 3.88/1.71  Reduction            : 0.17
% 3.88/1.71  Demodulation         : 0.13
% 3.88/1.71  BG Simplification    : 0.03
% 3.88/1.71  Subsumption          : 0.08
% 3.88/1.71  Abstraction          : 0.02
% 3.88/1.71  MUC search           : 0.00
% 3.88/1.71  Cooper               : 0.00
% 3.88/1.71  Total                : 0.92
% 3.88/1.71  Index Insertion      : 0.00
% 3.88/1.71  Index Deletion       : 0.00
% 3.88/1.71  Index Matching       : 0.00
% 3.88/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
