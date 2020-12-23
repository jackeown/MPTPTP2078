%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:56 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 307 expanded)
%              Number of leaves         :   37 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          :  284 (1315 expanded)
%              Number of equality atoms :   23 (  54 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_182,negated_conjecture,(
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

tff(f_84,axiom,(
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

tff(f_65,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ ( B != k1_xboole_0
                & m1_orders_2(B,A,B) )
            & ~ ( ~ m1_orders_2(B,A,B)
                & B = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_129,axiom,(
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
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_157,axiom,(
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
    ! [B_6] : ~ r2_xboole_0(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_42,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_40,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_71,plain,(
    ! [A_63,B_64] :
      ( r2_xboole_0(A_63,B_64)
      | B_64 = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_69,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_82,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_69])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_70,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_58])).

tff(c_98,plain,(
    ! [C_70,B_71,A_72] :
      ( r1_tarski(C_70,B_71)
      | ~ m1_orders_2(C_70,A_72,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_100,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_98])).

tff(c_103,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_100])).

tff(c_104,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_88,c_103])).

tff(c_36,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_118,plain,(
    ! [C_76,A_77,B_78] :
      ( m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m2_orders_2(C_76,A_77,B_78)
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_120,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_125,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_120])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_104,c_125])).

tff(c_128,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_130,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_70])).

tff(c_147,plain,(
    ! [B_82,A_83] :
      ( ~ m1_orders_2(B_82,A_83,B_82)
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_149,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_147])).

tff(c_152,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_149])).

tff(c_153,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_152])).

tff(c_161,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_169,plain,(
    ! [C_90,A_91,B_92] :
      ( m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m2_orders_2(C_90,A_91,B_92)
      | ~ m1_orders_1(B_92,k1_orders_1(u1_struct_0(A_91)))
      | ~ l1_orders_2(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v4_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_171,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_169])).

tff(c_174,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_171])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_161,c_174])).

tff(c_177,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_181,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_12])).

tff(c_216,plain,(
    ! [B_102,A_103,C_104] :
      ( r2_hidden(k1_funct_1(B_102,u1_struct_0(A_103)),C_104)
      | ~ m2_orders_2(C_104,A_103,B_102)
      | ~ m1_orders_1(B_102,k1_orders_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_229,plain,(
    ! [C_109,A_110,B_111] :
      ( ~ v1_xboole_0(C_109)
      | ~ m2_orders_2(C_109,A_110,B_111)
      | ~ m1_orders_1(B_111,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_231,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_234,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_181,c_231])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_234])).

tff(c_238,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r2_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_242,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_238,c_10])).

tff(c_245,plain,(
    ! [B_112,A_113] :
      ( B_112 = A_113
      | ~ r1_tarski(B_112,A_113)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_250,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_242,c_245])).

tff(c_255,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_285,plain,(
    ! [C_125,A_126,B_127] :
      ( m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m2_orders_2(C_125,A_126,B_127)
      | ~ m1_orders_1(B_127,k1_orders_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_289,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_285])).

tff(c_296,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_289])).

tff(c_297,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_296])).

tff(c_18,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_237,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_303,plain,(
    ! [C_131,A_132,D_133,B_134] :
      ( m1_orders_2(C_131,A_132,D_133)
      | m1_orders_2(D_133,A_132,C_131)
      | D_133 = C_131
      | ~ m2_orders_2(D_133,A_132,B_134)
      | ~ m2_orders_2(C_131,A_132,B_134)
      | ~ m1_orders_1(B_134,k1_orders_1(u1_struct_0(A_132)))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_305,plain,(
    ! [C_131] :
      ( m1_orders_2(C_131,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_131)
      | C_131 = '#skF_5'
      | ~ m2_orders_2(C_131,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_310,plain,(
    ! [C_131] :
      ( m1_orders_2(C_131,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_131)
      | C_131 = '#skF_5'
      | ~ m2_orders_2(C_131,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_305])).

tff(c_316,plain,(
    ! [C_135] :
      ( m1_orders_2(C_135,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_135)
      | C_135 = '#skF_5'
      | ~ m2_orders_2(C_135,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_310])).

tff(c_322,plain,
    ( m1_orders_2('#skF_4','#skF_2','#skF_5')
    | m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_316])).

tff(c_327,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_322])).

tff(c_328,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_332,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_255])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_332])).

tff(c_342,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_24,plain,(
    ! [C_19,B_17,A_13] :
      ( r1_tarski(C_19,B_17)
      | ~ m1_orders_2(C_19,A_13,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13)
      | ~ v4_orders_2(A_13)
      | ~ v3_orders_2(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_345,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_342,c_24])).

tff(c_348,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_297,c_345])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_255,c_348])).

tff(c_351,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_368,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_238])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.41  
% 2.55/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.41  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.55/1.41  
% 2.55/1.41  %Foreground sorts:
% 2.55/1.41  
% 2.55/1.41  
% 2.55/1.41  %Background operators:
% 2.55/1.41  
% 2.55/1.41  
% 2.55/1.41  %Foreground operators:
% 2.55/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.55/1.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.55/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.55/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.41  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.55/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.41  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.55/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.55/1.41  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.55/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.55/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.55/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.55/1.41  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.55/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.41  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.55/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.41  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.55/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.55/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.41  
% 2.55/1.43  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.55/1.43  tff(f_182, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 2.55/1.43  tff(f_84, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.55/1.43  tff(f_65, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.55/1.43  tff(f_110, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 2.55/1.43  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.55/1.43  tff(f_129, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.55/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.55/1.43  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.55/1.43  tff(f_157, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 2.55/1.43  tff(c_8, plain, (![B_6]: (~r2_xboole_0(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.43  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_42, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_40, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_71, plain, (![A_63, B_64]: (r2_xboole_0(A_63, B_64) | B_64=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.43  tff(c_52, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_69, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 2.55/1.43  tff(c_82, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_71, c_69])).
% 2.55/1.43  tff(c_88, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_82])).
% 2.55/1.43  tff(c_58, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_70, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_69, c_58])).
% 2.55/1.43  tff(c_98, plain, (![C_70, B_71, A_72]: (r1_tarski(C_70, B_71) | ~m1_orders_2(C_70, A_72, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.55/1.43  tff(c_100, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_98])).
% 2.55/1.43  tff(c_103, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_100])).
% 2.55/1.43  tff(c_104, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_88, c_103])).
% 2.55/1.43  tff(c_36, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_118, plain, (![C_76, A_77, B_78]: (m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~m2_orders_2(C_76, A_77, B_78) | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.43  tff(c_120, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_118])).
% 2.55/1.43  tff(c_125, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_120])).
% 2.55/1.43  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_104, c_125])).
% 2.55/1.43  tff(c_128, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_82])).
% 2.55/1.43  tff(c_130, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_70])).
% 2.55/1.43  tff(c_147, plain, (![B_82, A_83]: (~m1_orders_2(B_82, A_83, B_82) | k1_xboole_0=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.55/1.43  tff(c_149, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_130, c_147])).
% 2.55/1.43  tff(c_152, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_149])).
% 2.55/1.43  tff(c_153, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_152])).
% 2.55/1.43  tff(c_161, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_153])).
% 2.55/1.43  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.55/1.43  tff(c_169, plain, (![C_90, A_91, B_92]: (m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~m2_orders_2(C_90, A_91, B_92) | ~m1_orders_1(B_92, k1_orders_1(u1_struct_0(A_91))) | ~l1_orders_2(A_91) | ~v5_orders_2(A_91) | ~v4_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.43  tff(c_171, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_169])).
% 2.55/1.43  tff(c_174, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_171])).
% 2.55/1.43  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_161, c_174])).
% 2.55/1.43  tff(c_177, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_153])).
% 2.55/1.43  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.43  tff(c_181, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_12])).
% 2.55/1.43  tff(c_216, plain, (![B_102, A_103, C_104]: (r2_hidden(k1_funct_1(B_102, u1_struct_0(A_103)), C_104) | ~m2_orders_2(C_104, A_103, B_102) | ~m1_orders_1(B_102, k1_orders_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.55/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.43  tff(c_229, plain, (![C_109, A_110, B_111]: (~v1_xboole_0(C_109) | ~m2_orders_2(C_109, A_110, B_111) | ~m1_orders_1(B_111, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_216, c_2])).
% 2.55/1.43  tff(c_231, plain, (~v1_xboole_0('#skF_4') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_229])).
% 2.55/1.43  tff(c_234, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_181, c_231])).
% 2.55/1.43  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_234])).
% 2.55/1.43  tff(c_238, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.55/1.43  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.43  tff(c_242, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_238, c_10])).
% 2.55/1.43  tff(c_245, plain, (![B_112, A_113]: (B_112=A_113 | ~r1_tarski(B_112, A_113) | ~r1_tarski(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.43  tff(c_250, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_242, c_245])).
% 2.55/1.43  tff(c_255, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_250])).
% 2.55/1.43  tff(c_285, plain, (![C_125, A_126, B_127]: (m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m2_orders_2(C_125, A_126, B_127) | ~m1_orders_1(B_127, k1_orders_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.43  tff(c_289, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_285])).
% 2.55/1.43  tff(c_296, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_289])).
% 2.55/1.43  tff(c_297, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_296])).
% 2.55/1.43  tff(c_18, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.43  tff(c_237, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.55/1.43  tff(c_303, plain, (![C_131, A_132, D_133, B_134]: (m1_orders_2(C_131, A_132, D_133) | m1_orders_2(D_133, A_132, C_131) | D_133=C_131 | ~m2_orders_2(D_133, A_132, B_134) | ~m2_orders_2(C_131, A_132, B_134) | ~m1_orders_1(B_134, k1_orders_1(u1_struct_0(A_132))) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.43  tff(c_305, plain, (![C_131]: (m1_orders_2(C_131, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_131) | C_131='#skF_5' | ~m2_orders_2(C_131, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_303])).
% 2.55/1.43  tff(c_310, plain, (![C_131]: (m1_orders_2(C_131, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_131) | C_131='#skF_5' | ~m2_orders_2(C_131, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_305])).
% 2.55/1.43  tff(c_316, plain, (![C_135]: (m1_orders_2(C_135, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_135) | C_135='#skF_5' | ~m2_orders_2(C_135, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_310])).
% 2.55/1.43  tff(c_322, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_316])).
% 2.55/1.43  tff(c_327, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_237, c_322])).
% 2.55/1.43  tff(c_328, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_327])).
% 2.55/1.43  tff(c_332, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_328, c_255])).
% 2.55/1.43  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_332])).
% 2.55/1.43  tff(c_342, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_327])).
% 2.55/1.43  tff(c_24, plain, (![C_19, B_17, A_13]: (r1_tarski(C_19, B_17) | ~m1_orders_2(C_19, A_13, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_orders_2(A_13) | ~v5_orders_2(A_13) | ~v4_orders_2(A_13) | ~v3_orders_2(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.55/1.43  tff(c_345, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_342, c_24])).
% 2.55/1.43  tff(c_348, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_297, c_345])).
% 2.55/1.43  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_255, c_348])).
% 2.55/1.43  tff(c_351, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_250])).
% 2.55/1.43  tff(c_368, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_238])).
% 2.55/1.43  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_368])).
% 2.55/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.43  
% 2.55/1.43  Inference rules
% 2.55/1.43  ----------------------
% 2.55/1.43  #Ref     : 0
% 2.55/1.43  #Sup     : 43
% 2.55/1.43  #Fact    : 0
% 2.55/1.43  #Define  : 0
% 2.55/1.43  #Split   : 5
% 2.55/1.43  #Chain   : 0
% 2.55/1.43  #Close   : 0
% 2.55/1.43  
% 2.55/1.43  Ordering : KBO
% 2.55/1.43  
% 2.55/1.43  Simplification rules
% 2.55/1.43  ----------------------
% 2.55/1.43  #Subsume      : 2
% 2.55/1.43  #Demod        : 143
% 2.55/1.43  #Tautology    : 29
% 2.55/1.43  #SimpNegUnit  : 25
% 2.55/1.43  #BackRed      : 18
% 2.55/1.43  
% 2.55/1.43  #Partial instantiations: 0
% 2.55/1.43  #Strategies tried      : 1
% 2.55/1.43  
% 2.55/1.43  Timing (in seconds)
% 2.55/1.43  ----------------------
% 2.55/1.43  Preprocessing        : 0.35
% 2.55/1.43  Parsing              : 0.20
% 2.55/1.43  CNF conversion       : 0.03
% 2.55/1.43  Main loop            : 0.26
% 2.55/1.43  Inferencing          : 0.10
% 2.55/1.43  Reduction            : 0.08
% 2.55/1.43  Demodulation         : 0.06
% 2.55/1.43  BG Simplification    : 0.02
% 2.55/1.43  Subsumption          : 0.04
% 2.55/1.43  Abstraction          : 0.01
% 2.55/1.43  MUC search           : 0.00
% 2.55/1.44  Cooper               : 0.00
% 2.55/1.44  Total                : 0.65
% 2.55/1.44  Index Insertion      : 0.00
% 2.55/1.44  Index Deletion       : 0.00
% 2.55/1.44  Index Matching       : 0.00
% 2.55/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
