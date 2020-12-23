%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:59 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 301 expanded)
%              Number of leaves         :   35 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 (1260 expanded)
%              Number of equality atoms :   29 (  57 expanded)
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

tff(f_202,negated_conjecture,(
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

tff(f_82,axiom,(
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

tff(f_101,axiom,(
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

tff(f_126,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_149,axiom,(
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

tff(f_177,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_36,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_48,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_46,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_44,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_42,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_40,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_233,plain,(
    ! [C_116,A_117,B_118] :
      ( m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m2_orders_2(C_116,A_117,B_118)
      | ~ m1_orders_1(B_118,k1_orders_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_235,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_233])).

tff(c_238,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_235])).

tff(c_239,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_238])).

tff(c_87,plain,(
    ! [A_84,B_85] :
      ( r2_xboole_0(A_84,B_85)
      | B_85 = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_64,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_98,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_87,c_64])).

tff(c_104,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_70,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58])).

tff(c_151,plain,(
    ! [C_95,B_96,A_97] :
      ( r1_tarski(C_95,B_96)
      | ~ m1_orders_2(C_95,A_97,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_153,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_151])).

tff(c_156,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_153])).

tff(c_157,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_104,c_156])).

tff(c_165,plain,(
    ! [C_101,A_102,B_103] :
      ( m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m2_orders_2(C_101,A_102,B_103)
      | ~ m1_orders_1(B_103,k1_orders_1(u1_struct_0(A_102)))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102)
      | ~ v4_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_169,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_165])).

tff(c_176,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_169])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_157,c_176])).

tff(c_179,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_181,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_70])).

tff(c_264,plain,(
    ! [C_133,A_134,B_135] :
      ( ~ m1_orders_2(C_133,A_134,B_135)
      | ~ m1_orders_2(B_135,A_134,C_133)
      | k1_xboole_0 = B_135
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_266,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_181,c_264])).

tff(c_269,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_239,c_181,c_266])).

tff(c_270,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_269])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k1_xboole_0
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [B_80] : k4_xboole_0(B_80,B_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_18,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,(
    ! [B_80] : r1_xboole_0(k1_xboole_0,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_18])).

tff(c_247,plain,(
    ! [C_122,D_123,A_124,B_125] :
      ( ~ r1_xboole_0(C_122,D_123)
      | ~ m2_orders_2(D_123,A_124,B_125)
      | ~ m2_orders_2(C_122,A_124,B_125)
      | ~ m1_orders_1(B_125,k1_orders_1(u1_struct_0(A_124)))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_254,plain,(
    ! [B_126,A_127,B_128] :
      ( ~ m2_orders_2(B_126,A_127,B_128)
      | ~ m2_orders_2(k1_xboole_0,A_127,B_128)
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_76,c_247])).

tff(c_256,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_254])).

tff(c_259,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_256])).

tff(c_260,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_259])).

tff(c_272,plain,(
    ~ m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_260])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_272])).

tff(c_284,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_288,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_284,c_6])).

tff(c_324,plain,(
    ! [B_142,A_143] :
      ( B_142 = A_143
      | ~ r1_tarski(B_142,A_143)
      | ~ r1_tarski(A_143,B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_332,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_288,c_324])).

tff(c_337,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_38,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_396,plain,(
    ! [C_159,A_160,B_161] :
      ( m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ m2_orders_2(C_159,A_160,B_161)
      | ~ m1_orders_1(B_161,k1_orders_1(u1_struct_0(A_160)))
      | ~ l1_orders_2(A_160)
      | ~ v5_orders_2(A_160)
      | ~ v4_orders_2(A_160)
      | ~ v3_orders_2(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_398,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_396])).

tff(c_403,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_398])).

tff(c_404,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_403])).

tff(c_289,plain,(
    ! [A_136,B_137] :
      ( k4_xboole_0(A_136,B_137) = k1_xboole_0
      | ~ r1_tarski(A_136,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_297,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_289])).

tff(c_283,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_436,plain,(
    ! [C_180,A_181,D_182,B_183] :
      ( m1_orders_2(C_180,A_181,D_182)
      | m1_orders_2(D_182,A_181,C_180)
      | D_182 = C_180
      | ~ m2_orders_2(D_182,A_181,B_183)
      | ~ m2_orders_2(C_180,A_181,B_183)
      | ~ m1_orders_1(B_183,k1_orders_1(u1_struct_0(A_181)))
      | ~ l1_orders_2(A_181)
      | ~ v5_orders_2(A_181)
      | ~ v4_orders_2(A_181)
      | ~ v3_orders_2(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_438,plain,(
    ! [C_180] :
      ( m1_orders_2(C_180,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_180)
      | C_180 = '#skF_3'
      | ~ m2_orders_2(C_180,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_436])).

tff(c_443,plain,(
    ! [C_180] :
      ( m1_orders_2(C_180,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_180)
      | C_180 = '#skF_3'
      | ~ m2_orders_2(C_180,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_438])).

tff(c_449,plain,(
    ! [C_184] :
      ( m1_orders_2(C_184,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_184)
      | C_184 = '#skF_3'
      | ~ m2_orders_2(C_184,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_443])).

tff(c_455,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_449])).

tff(c_460,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_455])).

tff(c_461,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_341,plain,(
    k4_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_337])).

tff(c_477,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_341])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_477])).

tff(c_489,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_26,plain,(
    ! [C_23,B_21,A_17] :
      ( r1_tarski(C_23,B_21)
      | ~ m1_orders_2(C_23,A_17,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17)
      | ~ v4_orders_2(A_17)
      | ~ v3_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_498,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_489,c_26])).

tff(c_513,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_404,c_498])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_337,c_513])).

tff(c_516,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_521,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_284])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:30:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.51  
% 2.94/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.51  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.94/1.51  
% 2.94/1.51  %Foreground sorts:
% 2.94/1.51  
% 2.94/1.51  
% 2.94/1.51  %Background operators:
% 2.94/1.51  
% 2.94/1.51  
% 2.94/1.51  %Foreground operators:
% 2.94/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.51  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.94/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.51  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.94/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.51  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.94/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.94/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.51  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.94/1.51  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.94/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.51  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.94/1.51  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.94/1.51  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.94/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.51  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.94/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.51  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.94/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.51  
% 3.15/1.53  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.15/1.53  tff(f_202, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 3.15/1.53  tff(f_82, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.15/1.53  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.15/1.53  tff(f_126, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.15/1.53  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.53  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.15/1.53  tff(f_44, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.15/1.53  tff(f_149, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 3.15/1.53  tff(f_177, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 3.15/1.53  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.53  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_36, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_48, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_46, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_44, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_42, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_40, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_233, plain, (![C_116, A_117, B_118]: (m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~m2_orders_2(C_116, A_117, B_118) | ~m1_orders_1(B_118, k1_orders_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.53  tff(c_235, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_233])).
% 3.15/1.53  tff(c_238, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_235])).
% 3.15/1.53  tff(c_239, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_238])).
% 3.15/1.53  tff(c_87, plain, (![A_84, B_85]: (r2_xboole_0(A_84, B_85) | B_85=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.53  tff(c_52, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_64, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 3.15/1.53  tff(c_98, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_87, c_64])).
% 3.15/1.53  tff(c_104, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_98])).
% 3.15/1.53  tff(c_58, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_70, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_58])).
% 3.15/1.53  tff(c_151, plain, (![C_95, B_96, A_97]: (r1_tarski(C_95, B_96) | ~m1_orders_2(C_95, A_97, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.15/1.53  tff(c_153, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_151])).
% 3.15/1.53  tff(c_156, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_153])).
% 3.15/1.53  tff(c_157, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_104, c_156])).
% 3.15/1.53  tff(c_165, plain, (![C_101, A_102, B_103]: (m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~m2_orders_2(C_101, A_102, B_103) | ~m1_orders_1(B_103, k1_orders_1(u1_struct_0(A_102))) | ~l1_orders_2(A_102) | ~v5_orders_2(A_102) | ~v4_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.53  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_165])).
% 3.15/1.53  tff(c_176, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_169])).
% 3.15/1.53  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_157, c_176])).
% 3.15/1.53  tff(c_179, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_98])).
% 3.15/1.53  tff(c_181, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_70])).
% 3.15/1.53  tff(c_264, plain, (![C_133, A_134, B_135]: (~m1_orders_2(C_133, A_134, B_135) | ~m1_orders_2(B_135, A_134, C_133) | k1_xboole_0=B_135 | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.15/1.53  tff(c_266, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_181, c_264])).
% 3.15/1.53  tff(c_269, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_239, c_181, c_266])).
% 3.15/1.53  tff(c_270, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_269])).
% 3.15/1.53  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.53  tff(c_65, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k1_xboole_0 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.53  tff(c_71, plain, (![B_80]: (k4_xboole_0(B_80, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_65])).
% 3.15/1.53  tff(c_18, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.53  tff(c_76, plain, (![B_80]: (r1_xboole_0(k1_xboole_0, B_80))), inference(superposition, [status(thm), theory('equality')], [c_71, c_18])).
% 3.15/1.53  tff(c_247, plain, (![C_122, D_123, A_124, B_125]: (~r1_xboole_0(C_122, D_123) | ~m2_orders_2(D_123, A_124, B_125) | ~m2_orders_2(C_122, A_124, B_125) | ~m1_orders_1(B_125, k1_orders_1(u1_struct_0(A_124))) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.53  tff(c_254, plain, (![B_126, A_127, B_128]: (~m2_orders_2(B_126, A_127, B_128) | ~m2_orders_2(k1_xboole_0, A_127, B_128) | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_76, c_247])).
% 3.15/1.53  tff(c_256, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_254])).
% 3.15/1.53  tff(c_259, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_256])).
% 3.15/1.53  tff(c_260, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_259])).
% 3.15/1.53  tff(c_272, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_260])).
% 3.15/1.53  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_272])).
% 3.15/1.53  tff(c_284, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.15/1.53  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.53  tff(c_288, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_284, c_6])).
% 3.15/1.53  tff(c_324, plain, (![B_142, A_143]: (B_142=A_143 | ~r1_tarski(B_142, A_143) | ~r1_tarski(A_143, B_142))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.53  tff(c_332, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_288, c_324])).
% 3.15/1.53  tff(c_337, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_332])).
% 3.15/1.53  tff(c_38, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.15/1.53  tff(c_396, plain, (![C_159, A_160, B_161]: (m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(A_160))) | ~m2_orders_2(C_159, A_160, B_161) | ~m1_orders_1(B_161, k1_orders_1(u1_struct_0(A_160))) | ~l1_orders_2(A_160) | ~v5_orders_2(A_160) | ~v4_orders_2(A_160) | ~v3_orders_2(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.53  tff(c_398, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_396])).
% 3.15/1.53  tff(c_403, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_398])).
% 3.15/1.53  tff(c_404, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_403])).
% 3.15/1.53  tff(c_289, plain, (![A_136, B_137]: (k4_xboole_0(A_136, B_137)=k1_xboole_0 | ~r1_tarski(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.53  tff(c_297, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_289])).
% 3.15/1.53  tff(c_283, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.15/1.53  tff(c_436, plain, (![C_180, A_181, D_182, B_183]: (m1_orders_2(C_180, A_181, D_182) | m1_orders_2(D_182, A_181, C_180) | D_182=C_180 | ~m2_orders_2(D_182, A_181, B_183) | ~m2_orders_2(C_180, A_181, B_183) | ~m1_orders_1(B_183, k1_orders_1(u1_struct_0(A_181))) | ~l1_orders_2(A_181) | ~v5_orders_2(A_181) | ~v4_orders_2(A_181) | ~v3_orders_2(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.15/1.53  tff(c_438, plain, (![C_180]: (m1_orders_2(C_180, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_180) | C_180='#skF_3' | ~m2_orders_2(C_180, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_436])).
% 3.15/1.53  tff(c_443, plain, (![C_180]: (m1_orders_2(C_180, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_180) | C_180='#skF_3' | ~m2_orders_2(C_180, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_438])).
% 3.15/1.53  tff(c_449, plain, (![C_184]: (m1_orders_2(C_184, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_184) | C_184='#skF_3' | ~m2_orders_2(C_184, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_443])).
% 3.15/1.53  tff(c_455, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_449])).
% 3.15/1.53  tff(c_460, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_283, c_455])).
% 3.15/1.53  tff(c_461, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_460])).
% 3.15/1.53  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.53  tff(c_341, plain, (k4_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_337])).
% 3.15/1.53  tff(c_477, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_461, c_341])).
% 3.15/1.53  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_477])).
% 3.15/1.53  tff(c_489, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_460])).
% 3.15/1.53  tff(c_26, plain, (![C_23, B_21, A_17]: (r1_tarski(C_23, B_21) | ~m1_orders_2(C_23, A_17, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_orders_2(A_17) | ~v5_orders_2(A_17) | ~v4_orders_2(A_17) | ~v3_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.15/1.53  tff(c_498, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_489, c_26])).
% 3.15/1.53  tff(c_513, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_404, c_498])).
% 3.15/1.53  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_337, c_513])).
% 3.15/1.53  tff(c_516, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_332])).
% 3.15/1.53  tff(c_521, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_284])).
% 3.15/1.53  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_521])).
% 3.15/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.53  
% 3.15/1.53  Inference rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Ref     : 0
% 3.15/1.53  #Sup     : 77
% 3.15/1.53  #Fact    : 0
% 3.15/1.53  #Define  : 0
% 3.15/1.53  #Split   : 4
% 3.15/1.53  #Chain   : 0
% 3.15/1.53  #Close   : 0
% 3.15/1.53  
% 3.15/1.53  Ordering : KBO
% 3.15/1.53  
% 3.15/1.53  Simplification rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Subsume      : 11
% 3.15/1.53  #Demod        : 174
% 3.15/1.53  #Tautology    : 39
% 3.15/1.53  #SimpNegUnit  : 29
% 3.15/1.53  #BackRed      : 27
% 3.15/1.53  
% 3.15/1.53  #Partial instantiations: 0
% 3.15/1.53  #Strategies tried      : 1
% 3.15/1.53  
% 3.15/1.53  Timing (in seconds)
% 3.15/1.53  ----------------------
% 3.15/1.53  Preprocessing        : 0.36
% 3.15/1.53  Parsing              : 0.21
% 3.15/1.53  CNF conversion       : 0.03
% 3.15/1.54  Main loop            : 0.32
% 3.15/1.54  Inferencing          : 0.12
% 3.15/1.54  Reduction            : 0.10
% 3.15/1.54  Demodulation         : 0.07
% 3.15/1.54  BG Simplification    : 0.02
% 3.15/1.54  Subsumption          : 0.06
% 3.15/1.54  Abstraction          : 0.01
% 3.15/1.54  MUC search           : 0.00
% 3.15/1.54  Cooper               : 0.00
% 3.15/1.54  Total                : 0.73
% 3.15/1.54  Index Insertion      : 0.00
% 3.15/1.54  Index Deletion       : 0.00
% 3.15/1.54  Index Matching       : 0.00
% 3.15/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
