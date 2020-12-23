%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:00 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 299 expanded)
%              Number of leaves         :   36 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  296 (1268 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

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

tff(f_93,axiom,(
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

tff(f_112,axiom,(
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

tff(f_137,axiom,(
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

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
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

tff(c_205,plain,(
    ! [C_116,A_117,B_118] :
      ( m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m2_orders_2(C_116,A_117,B_118)
      | ~ m1_orders_1(B_118,k1_orders_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_207,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_205])).

tff(c_210,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_207])).

tff(c_211,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_210])).

tff(c_106,plain,(
    ! [A_83,B_84] :
      ( r2_xboole_0(A_83,B_84)
      | B_84 = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_70,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_72,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56])).

tff(c_117,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_72])).

tff(c_123,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_131,plain,(
    ! [C_88,B_89,A_90] :
      ( r1_tarski(C_88,B_89)
      | ~ m1_orders_2(C_88,A_90,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_133,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_131])).

tff(c_136,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_133])).

tff(c_137,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_123,c_136])).

tff(c_157,plain,(
    ! [C_99,A_100,B_101] :
      ( m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m2_orders_2(C_99,A_100,B_101)
      | ~ m1_orders_1(B_101,k1_orders_1(u1_struct_0(A_100)))
      | ~ l1_orders_2(A_100)
      | ~ v5_orders_2(A_100)
      | ~ v4_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_161,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_157])).

tff(c_168,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_161])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_137,c_168])).

tff(c_171,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_174,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_70])).

tff(c_263,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_265,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_174,c_263])).

tff(c_268,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_211,c_174,c_265])).

tff(c_269,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_268])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_73])).

tff(c_231,plain,(
    ! [B_123,A_124,C_125] :
      ( r2_hidden(k1_funct_1(B_123,u1_struct_0(A_124)),C_125)
      | ~ m2_orders_2(C_125,A_124,B_123)
      | ~ m1_orders_1(B_123,k1_orders_1(u1_struct_0(A_124)))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_243,plain,(
    ! [C_126,B_127,A_128] :
      ( ~ r1_tarski(C_126,k1_funct_1(B_127,u1_struct_0(A_128)))
      | ~ m2_orders_2(C_126,A_128,B_127)
      | ~ m1_orders_1(B_127,k1_orders_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_231,c_22])).

tff(c_254,plain,(
    ! [A_129,B_130] :
      ( ~ m2_orders_2(k1_xboole_0,A_129,B_130)
      | ~ m1_orders_1(B_130,k1_orders_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_81,c_243])).

tff(c_257,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_254])).

tff(c_260,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_257])).

tff(c_261,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_260])).

tff(c_271,plain,(
    ~ m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_261])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_271])).

tff(c_280,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_285,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_280,c_6])).

tff(c_298,plain,(
    ! [B_139,A_140] :
      ( B_139 = A_140
      | ~ r1_tarski(B_139,A_140)
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_306,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_298])).

tff(c_337,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_361,plain,(
    ! [C_158,A_159,B_160] :
      ( m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m2_orders_2(C_158,A_159,B_160)
      | ~ m1_orders_1(B_160,k1_orders_1(u1_struct_0(A_159)))
      | ~ l1_orders_2(A_159)
      | ~ v5_orders_2(A_159)
      | ~ v4_orders_2(A_159)
      | ~ v3_orders_2(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_363,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_361])).

tff(c_368,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_363])).

tff(c_369,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_368])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_287,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_56])).

tff(c_493,plain,(
    ! [C_205,A_206,D_207,B_208] :
      ( m1_orders_2(C_205,A_206,D_207)
      | m1_orders_2(D_207,A_206,C_205)
      | D_207 = C_205
      | ~ m2_orders_2(D_207,A_206,B_208)
      | ~ m2_orders_2(C_205,A_206,B_208)
      | ~ m1_orders_1(B_208,k1_orders_1(u1_struct_0(A_206)))
      | ~ l1_orders_2(A_206)
      | ~ v5_orders_2(A_206)
      | ~ v4_orders_2(A_206)
      | ~ v3_orders_2(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_495,plain,(
    ! [C_205] :
      ( m1_orders_2(C_205,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_205)
      | C_205 = '#skF_3'
      | ~ m2_orders_2(C_205,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_493])).

tff(c_500,plain,(
    ! [C_205] :
      ( m1_orders_2(C_205,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_205)
      | C_205 = '#skF_3'
      | ~ m2_orders_2(C_205,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_495])).

tff(c_506,plain,(
    ! [C_209] :
      ( m1_orders_2(C_209,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_209)
      | C_209 = '#skF_3'
      | ~ m2_orders_2(C_209,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_500])).

tff(c_512,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_506])).

tff(c_517,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_512])).

tff(c_518,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_527,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_337])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_527])).

tff(c_538,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_517])).

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
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_559,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_538,c_30])).

tff(c_574,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_369,c_559])).

tff(c_576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_337,c_574])).

tff(c_577,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_581,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_280])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.43  
% 2.94/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.43  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.94/1.43  
% 2.94/1.43  %Foreground sorts:
% 2.94/1.43  
% 2.94/1.43  
% 2.94/1.43  %Background operators:
% 2.94/1.43  
% 2.94/1.43  
% 2.94/1.43  %Foreground operators:
% 2.94/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.43  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.43  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.94/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.43  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.94/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.43  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.94/1.43  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.94/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.43  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.94/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.94/1.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.94/1.43  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.43  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.94/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.43  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.94/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.43  
% 2.94/1.45  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.94/1.45  tff(f_209, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.94/1.45  tff(f_93, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.94/1.45  tff(f_112, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.94/1.45  tff(f_137, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.94/1.45  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.94/1.45  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.94/1.45  tff(f_156, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.94/1.45  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.94/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.45  tff(f_184, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.94/1.45  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.94/1.45  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_205, plain, (![C_116, A_117, B_118]: (m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~m2_orders_2(C_116, A_117, B_118) | ~m1_orders_1(B_118, k1_orders_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.45  tff(c_207, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_205])).
% 2.94/1.45  tff(c_210, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_207])).
% 2.94/1.45  tff(c_211, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_210])).
% 2.94/1.45  tff(c_106, plain, (![A_83, B_84]: (r2_xboole_0(A_83, B_84) | B_84=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.94/1.45  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_70, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 2.94/1.45  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_72, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56])).
% 2.94/1.45  tff(c_117, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_106, c_72])).
% 2.94/1.45  tff(c_123, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_117])).
% 2.94/1.45  tff(c_131, plain, (![C_88, B_89, A_90]: (r1_tarski(C_88, B_89) | ~m1_orders_2(C_88, A_90, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.94/1.45  tff(c_133, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_131])).
% 2.94/1.45  tff(c_136, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_133])).
% 2.94/1.45  tff(c_137, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_123, c_136])).
% 2.94/1.45  tff(c_157, plain, (![C_99, A_100, B_101]: (m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~m2_orders_2(C_99, A_100, B_101) | ~m1_orders_1(B_101, k1_orders_1(u1_struct_0(A_100))) | ~l1_orders_2(A_100) | ~v5_orders_2(A_100) | ~v4_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.45  tff(c_161, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_157])).
% 2.94/1.45  tff(c_168, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_161])).
% 2.94/1.45  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_137, c_168])).
% 2.94/1.45  tff(c_171, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_117])).
% 2.94/1.45  tff(c_174, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_70])).
% 2.94/1.45  tff(c_263, plain, (![C_133, A_134, B_135]: (~m1_orders_2(C_133, A_134, B_135) | ~m1_orders_2(B_135, A_134, C_133) | k1_xboole_0=B_135 | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.94/1.45  tff(c_265, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_174, c_263])).
% 2.94/1.45  tff(c_268, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_211, c_174, c_265])).
% 2.94/1.45  tff(c_269, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_268])).
% 2.94/1.45  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.94/1.45  tff(c_73, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(B_78)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.94/1.45  tff(c_81, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_73])).
% 2.94/1.45  tff(c_231, plain, (![B_123, A_124, C_125]: (r2_hidden(k1_funct_1(B_123, u1_struct_0(A_124)), C_125) | ~m2_orders_2(C_125, A_124, B_123) | ~m1_orders_1(B_123, k1_orders_1(u1_struct_0(A_124))) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.94/1.45  tff(c_22, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.45  tff(c_243, plain, (![C_126, B_127, A_128]: (~r1_tarski(C_126, k1_funct_1(B_127, u1_struct_0(A_128))) | ~m2_orders_2(C_126, A_128, B_127) | ~m1_orders_1(B_127, k1_orders_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(resolution, [status(thm)], [c_231, c_22])).
% 2.94/1.45  tff(c_254, plain, (![A_129, B_130]: (~m2_orders_2(k1_xboole_0, A_129, B_130) | ~m1_orders_1(B_130, k1_orders_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(resolution, [status(thm)], [c_81, c_243])).
% 2.94/1.45  tff(c_257, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_254])).
% 2.94/1.45  tff(c_260, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_257])).
% 2.94/1.45  tff(c_261, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_260])).
% 2.94/1.45  tff(c_271, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_261])).
% 2.94/1.45  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_271])).
% 2.94/1.45  tff(c_280, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 2.94/1.45  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.94/1.45  tff(c_285, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_280, c_6])).
% 2.94/1.45  tff(c_298, plain, (![B_139, A_140]: (B_139=A_140 | ~r1_tarski(B_139, A_140) | ~r1_tarski(A_140, B_139))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.94/1.45  tff(c_306, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_285, c_298])).
% 2.94/1.45  tff(c_337, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_306])).
% 2.94/1.45  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.94/1.45  tff(c_361, plain, (![C_158, A_159, B_160]: (m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~m2_orders_2(C_158, A_159, B_160) | ~m1_orders_1(B_160, k1_orders_1(u1_struct_0(A_159))) | ~l1_orders_2(A_159) | ~v5_orders_2(A_159) | ~v4_orders_2(A_159) | ~v3_orders_2(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.45  tff(c_363, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_361])).
% 2.94/1.45  tff(c_368, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_363])).
% 2.94/1.45  tff(c_369, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_368])).
% 2.94/1.45  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.94/1.45  tff(c_287, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_56])).
% 2.94/1.45  tff(c_493, plain, (![C_205, A_206, D_207, B_208]: (m1_orders_2(C_205, A_206, D_207) | m1_orders_2(D_207, A_206, C_205) | D_207=C_205 | ~m2_orders_2(D_207, A_206, B_208) | ~m2_orders_2(C_205, A_206, B_208) | ~m1_orders_1(B_208, k1_orders_1(u1_struct_0(A_206))) | ~l1_orders_2(A_206) | ~v5_orders_2(A_206) | ~v4_orders_2(A_206) | ~v3_orders_2(A_206) | v2_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.94/1.45  tff(c_495, plain, (![C_205]: (m1_orders_2(C_205, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_205) | C_205='#skF_3' | ~m2_orders_2(C_205, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_493])).
% 2.94/1.45  tff(c_500, plain, (![C_205]: (m1_orders_2(C_205, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_205) | C_205='#skF_3' | ~m2_orders_2(C_205, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_495])).
% 2.94/1.45  tff(c_506, plain, (![C_209]: (m1_orders_2(C_209, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_209) | C_209='#skF_3' | ~m2_orders_2(C_209, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_500])).
% 2.94/1.45  tff(c_512, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_506])).
% 2.94/1.45  tff(c_517, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_287, c_512])).
% 2.94/1.45  tff(c_518, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_517])).
% 2.94/1.45  tff(c_527, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_518, c_337])).
% 2.94/1.45  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_527])).
% 2.94/1.45  tff(c_538, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_517])).
% 2.94/1.45  tff(c_30, plain, (![C_27, B_25, A_21]: (r1_tarski(C_27, B_25) | ~m1_orders_2(C_27, A_21, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_orders_2(A_21) | ~v5_orders_2(A_21) | ~v4_orders_2(A_21) | ~v3_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.94/1.45  tff(c_559, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_538, c_30])).
% 2.94/1.45  tff(c_574, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_369, c_559])).
% 2.94/1.45  tff(c_576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_337, c_574])).
% 2.94/1.45  tff(c_577, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_306])).
% 2.94/1.45  tff(c_581, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_280])).
% 2.94/1.45  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_581])).
% 2.94/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  Inference rules
% 2.94/1.45  ----------------------
% 2.94/1.45  #Ref     : 0
% 2.94/1.45  #Sup     : 86
% 2.94/1.45  #Fact    : 0
% 2.94/1.45  #Define  : 0
% 2.94/1.45  #Split   : 8
% 2.94/1.45  #Chain   : 0
% 2.94/1.45  #Close   : 0
% 2.94/1.45  
% 2.94/1.45  Ordering : KBO
% 2.94/1.45  
% 2.94/1.45  Simplification rules
% 2.94/1.45  ----------------------
% 2.94/1.45  #Subsume      : 10
% 2.94/1.45  #Demod        : 160
% 2.94/1.45  #Tautology    : 28
% 2.94/1.45  #SimpNegUnit  : 26
% 2.94/1.45  #BackRed      : 27
% 2.94/1.45  
% 2.94/1.45  #Partial instantiations: 0
% 2.94/1.45  #Strategies tried      : 1
% 2.94/1.45  
% 2.94/1.45  Timing (in seconds)
% 2.94/1.45  ----------------------
% 2.94/1.45  Preprocessing        : 0.33
% 2.94/1.45  Parsing              : 0.18
% 2.94/1.45  CNF conversion       : 0.03
% 2.94/1.45  Main loop            : 0.34
% 2.94/1.45  Inferencing          : 0.13
% 2.94/1.45  Reduction            : 0.11
% 2.94/1.45  Demodulation         : 0.07
% 2.94/1.45  BG Simplification    : 0.02
% 2.94/1.45  Subsumption          : 0.06
% 2.94/1.45  Abstraction          : 0.01
% 2.94/1.45  MUC search           : 0.00
% 2.94/1.45  Cooper               : 0.00
% 2.94/1.45  Total                : 0.71
% 2.94/1.45  Index Insertion      : 0.00
% 2.94/1.45  Index Deletion       : 0.00
% 2.94/1.45  Index Matching       : 0.00
% 2.94/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
