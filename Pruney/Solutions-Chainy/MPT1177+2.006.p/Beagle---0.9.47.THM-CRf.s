%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:55 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 298 expanded)
%              Number of leaves         :   39 ( 126 expanded)
%              Depth                    :   10
%              Number of atoms          :  294 (1244 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_208,negated_conjecture,(
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

tff(f_155,axiom,(
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

tff(f_92,axiom,(
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

tff(f_111,axiom,(
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

tff(f_136,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_183,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_50,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_48,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_46,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_44,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_42,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_190,plain,(
    ! [B_106,A_107,C_108] :
      ( r2_hidden(k1_funct_1(B_106,u1_struct_0(A_107)),C_108)
      | ~ m2_orders_2(C_108,A_107,B_106)
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0(A_107)))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_195,plain,(
    ! [C_109,A_110,B_111] :
      ( ~ v1_xboole_0(C_109)
      | ~ m2_orders_2(C_109,A_110,B_111)
      | ~ m1_orders_1(B_111,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_190,c_2])).

tff(c_197,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_195])).

tff(c_200,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_197])).

tff(c_201,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_200])).

tff(c_183,plain,(
    ! [C_103,A_104,B_105] :
      ( m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m2_orders_2(C_103,A_104,B_105)
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_185,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_183])).

tff(c_188,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_185])).

tff(c_189,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_188])).

tff(c_86,plain,(
    ! [A_79,B_80] :
      ( r2_xboole_0(A_79,B_80)
      | B_80 = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_72,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_97,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_72])).

tff(c_109,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_60,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_73,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60])).

tff(c_123,plain,(
    ! [C_85,B_86,A_87] :
      ( r1_tarski(C_85,B_86)
      | ~ m1_orders_2(C_85,A_87,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_125,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_123])).

tff(c_128,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_125])).

tff(c_129,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_109,c_128])).

tff(c_38,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_137,plain,(
    ! [C_91,A_92,B_93] :
      ( m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m2_orders_2(C_91,A_92,B_93)
      | ~ m1_orders_1(B_93,k1_orders_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_141,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_148,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_141])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_129,c_148])).

tff(c_151,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_153,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_73])).

tff(c_202,plain,(
    ! [C_112,A_113,B_114] :
      ( ~ m1_orders_2(C_112,A_113,B_114)
      | ~ m1_orders_2(B_114,A_113,C_112)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_204,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_153,c_202])).

tff(c_207,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_189,c_153,c_204])).

tff(c_208,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_207])).

tff(c_16,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [B_77,A_78] :
      ( ~ r1_xboole_0(B_77,A_78)
      | ~ r1_tarski(B_77,A_78)
      | v1_xboole_0(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    ! [A_81] :
      ( ~ r1_tarski(A_81,k1_xboole_0)
      | v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_18,c_81])).

tff(c_108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_103])).

tff(c_210,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_108])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_210])).

tff(c_216,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r2_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_220,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_216,c_10])).

tff(c_223,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ r1_tarski(B_115,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_228,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_223])).

tff(c_233,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_272,plain,(
    ! [C_128,A_129,B_130] :
      ( m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m2_orders_2(C_128,A_129,B_130)
      | ~ m1_orders_1(B_130,k1_orders_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_274,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_272])).

tff(c_279,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_274])).

tff(c_280,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_279])).

tff(c_215,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_305,plain,(
    ! [C_143,A_144,D_145,B_146] :
      ( m1_orders_2(C_143,A_144,D_145)
      | m1_orders_2(D_145,A_144,C_143)
      | D_145 = C_143
      | ~ m2_orders_2(D_145,A_144,B_146)
      | ~ m2_orders_2(C_143,A_144,B_146)
      | ~ m1_orders_1(B_146,k1_orders_1(u1_struct_0(A_144)))
      | ~ l1_orders_2(A_144)
      | ~ v5_orders_2(A_144)
      | ~ v4_orders_2(A_144)
      | ~ v3_orders_2(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_307,plain,(
    ! [C_143] :
      ( m1_orders_2(C_143,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_143)
      | C_143 = '#skF_4'
      | ~ m2_orders_2(C_143,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_305])).

tff(c_312,plain,(
    ! [C_143] :
      ( m1_orders_2(C_143,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_143)
      | C_143 = '#skF_4'
      | ~ m2_orders_2(C_143,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_307])).

tff(c_318,plain,(
    ! [C_147] :
      ( m1_orders_2(C_147,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_147)
      | C_147 = '#skF_4'
      | ~ m2_orders_2(C_147,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_312])).

tff(c_324,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_318])).

tff(c_329,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_324])).

tff(c_330,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_334,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_233])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_334])).

tff(c_344,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_28,plain,(
    ! [C_26,B_24,A_20] :
      ( r1_tarski(C_26,B_24)
      | ~ m1_orders_2(C_26,A_20,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20)
      | ~ v4_orders_2(A_20)
      | ~ v3_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_351,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_344,c_28])).

tff(c_362,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_280,c_351])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_233,c_362])).

tff(c_365,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_382,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_216])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.46  
% 2.73/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.46  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.73/1.46  
% 2.73/1.46  %Foreground sorts:
% 2.73/1.46  
% 2.73/1.46  
% 2.73/1.46  %Background operators:
% 2.73/1.46  
% 2.73/1.46  
% 2.73/1.46  %Foreground operators:
% 2.73/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.73/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.46  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.73/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.46  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.73/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.73/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.73/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.46  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.73/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.73/1.46  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.73/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.46  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.73/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.46  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.73/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.46  
% 2.88/1.49  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.88/1.49  tff(f_208, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 2.88/1.49  tff(f_155, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.88/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.88/1.49  tff(f_92, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.88/1.49  tff(f_111, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.88/1.49  tff(f_136, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 2.88/1.49  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.88/1.49  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.88/1.49  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.88/1.49  tff(f_183, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 2.88/1.49  tff(c_8, plain, (![B_6]: (~r2_xboole_0(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.49  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_50, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_48, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_46, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_44, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_42, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_190, plain, (![B_106, A_107, C_108]: (r2_hidden(k1_funct_1(B_106, u1_struct_0(A_107)), C_108) | ~m2_orders_2(C_108, A_107, B_106) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0(A_107))) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.88/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.49  tff(c_195, plain, (![C_109, A_110, B_111]: (~v1_xboole_0(C_109) | ~m2_orders_2(C_109, A_110, B_111) | ~m1_orders_1(B_111, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_190, c_2])).
% 2.88/1.49  tff(c_197, plain, (~v1_xboole_0('#skF_4') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_195])).
% 2.88/1.49  tff(c_200, plain, (~v1_xboole_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_197])).
% 2.88/1.49  tff(c_201, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_200])).
% 2.88/1.49  tff(c_183, plain, (![C_103, A_104, B_105]: (m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~m2_orders_2(C_103, A_104, B_105) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.88/1.49  tff(c_185, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_183])).
% 2.88/1.49  tff(c_188, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_185])).
% 2.88/1.49  tff(c_189, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_188])).
% 2.88/1.49  tff(c_86, plain, (![A_79, B_80]: (r2_xboole_0(A_79, B_80) | B_80=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.49  tff(c_54, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_72, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 2.88/1.49  tff(c_97, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_86, c_72])).
% 2.88/1.49  tff(c_109, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_97])).
% 2.88/1.49  tff(c_60, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_73, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_60])).
% 2.88/1.49  tff(c_123, plain, (![C_85, B_86, A_87]: (r1_tarski(C_85, B_86) | ~m1_orders_2(C_85, A_87, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.88/1.49  tff(c_125, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_73, c_123])).
% 2.88/1.49  tff(c_128, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_125])).
% 2.88/1.49  tff(c_129, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_109, c_128])).
% 2.88/1.49  tff(c_38, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 2.88/1.49  tff(c_137, plain, (![C_91, A_92, B_93]: (m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~m2_orders_2(C_91, A_92, B_93) | ~m1_orders_1(B_93, k1_orders_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.88/1.49  tff(c_141, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_137])).
% 2.88/1.49  tff(c_148, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_141])).
% 2.88/1.49  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_129, c_148])).
% 2.88/1.49  tff(c_151, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_97])).
% 2.88/1.49  tff(c_153, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_73])).
% 2.88/1.49  tff(c_202, plain, (![C_112, A_113, B_114]: (~m1_orders_2(C_112, A_113, B_114) | ~m1_orders_2(B_114, A_113, C_112) | k1_xboole_0=B_114 | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.88/1.49  tff(c_204, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_153, c_202])).
% 2.88/1.49  tff(c_207, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_189, c_153, c_204])).
% 2.88/1.49  tff(c_208, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_207])).
% 2.88/1.49  tff(c_16, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.49  tff(c_18, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.88/1.49  tff(c_81, plain, (![B_77, A_78]: (~r1_xboole_0(B_77, A_78) | ~r1_tarski(B_77, A_78) | v1_xboole_0(B_77))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.88/1.49  tff(c_103, plain, (![A_81]: (~r1_tarski(A_81, k1_xboole_0) | v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_18, c_81])).
% 2.88/1.49  tff(c_108, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_103])).
% 2.88/1.49  tff(c_210, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_108])).
% 2.88/1.49  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_210])).
% 2.88/1.49  tff(c_216, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 2.88/1.49  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.49  tff(c_220, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_216, c_10])).
% 2.88/1.49  tff(c_223, plain, (![B_115, A_116]: (B_115=A_116 | ~r1_tarski(B_115, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.49  tff(c_228, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_220, c_223])).
% 2.88/1.49  tff(c_233, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_228])).
% 2.88/1.49  tff(c_272, plain, (![C_128, A_129, B_130]: (m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~m2_orders_2(C_128, A_129, B_130) | ~m1_orders_1(B_130, k1_orders_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.88/1.49  tff(c_274, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_272])).
% 2.88/1.49  tff(c_279, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_274])).
% 2.88/1.49  tff(c_280, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_279])).
% 2.88/1.49  tff(c_215, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 2.88/1.49  tff(c_305, plain, (![C_143, A_144, D_145, B_146]: (m1_orders_2(C_143, A_144, D_145) | m1_orders_2(D_145, A_144, C_143) | D_145=C_143 | ~m2_orders_2(D_145, A_144, B_146) | ~m2_orders_2(C_143, A_144, B_146) | ~m1_orders_1(B_146, k1_orders_1(u1_struct_0(A_144))) | ~l1_orders_2(A_144) | ~v5_orders_2(A_144) | ~v4_orders_2(A_144) | ~v3_orders_2(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_183])).
% 2.88/1.49  tff(c_307, plain, (![C_143]: (m1_orders_2(C_143, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_143) | C_143='#skF_4' | ~m2_orders_2(C_143, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_305])).
% 2.88/1.49  tff(c_312, plain, (![C_143]: (m1_orders_2(C_143, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_143) | C_143='#skF_4' | ~m2_orders_2(C_143, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_307])).
% 2.88/1.49  tff(c_318, plain, (![C_147]: (m1_orders_2(C_147, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_147) | C_147='#skF_4' | ~m2_orders_2(C_147, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_312])).
% 2.88/1.49  tff(c_324, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_318])).
% 2.88/1.49  tff(c_329, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_215, c_324])).
% 2.88/1.49  tff(c_330, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_329])).
% 2.88/1.49  tff(c_334, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_233])).
% 2.88/1.49  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_334])).
% 2.88/1.49  tff(c_344, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_329])).
% 2.88/1.49  tff(c_28, plain, (![C_26, B_24, A_20]: (r1_tarski(C_26, B_24) | ~m1_orders_2(C_26, A_20, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.88/1.49  tff(c_351, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_344, c_28])).
% 2.88/1.49  tff(c_362, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_280, c_351])).
% 2.88/1.49  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_233, c_362])).
% 2.88/1.49  tff(c_365, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_228])).
% 2.88/1.49  tff(c_382, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_216])).
% 2.88/1.49  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_382])).
% 2.88/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.49  
% 2.88/1.49  Inference rules
% 2.88/1.49  ----------------------
% 2.88/1.49  #Ref     : 0
% 2.88/1.49  #Sup     : 45
% 2.88/1.49  #Fact    : 0
% 2.88/1.49  #Define  : 0
% 2.88/1.49  #Split   : 4
% 2.88/1.49  #Chain   : 0
% 2.88/1.49  #Close   : 0
% 2.88/1.49  
% 2.88/1.49  Ordering : KBO
% 2.88/1.49  
% 2.88/1.49  Simplification rules
% 2.88/1.49  ----------------------
% 2.88/1.49  #Subsume      : 4
% 2.88/1.49  #Demod        : 148
% 2.88/1.49  #Tautology    : 24
% 2.88/1.49  #SimpNegUnit  : 28
% 2.88/1.49  #BackRed      : 19
% 2.88/1.49  
% 2.88/1.49  #Partial instantiations: 0
% 2.88/1.49  #Strategies tried      : 1
% 2.88/1.49  
% 2.88/1.49  Timing (in seconds)
% 2.88/1.49  ----------------------
% 2.88/1.49  Preprocessing        : 0.32
% 2.88/1.49  Parsing              : 0.18
% 2.88/1.49  CNF conversion       : 0.03
% 2.88/1.49  Main loop            : 0.32
% 2.88/1.49  Inferencing          : 0.11
% 2.88/1.49  Reduction            : 0.10
% 2.88/1.49  Demodulation         : 0.08
% 2.88/1.49  BG Simplification    : 0.02
% 2.88/1.49  Subsumption          : 0.06
% 2.88/1.49  Abstraction          : 0.01
% 2.88/1.49  MUC search           : 0.00
% 2.88/1.49  Cooper               : 0.00
% 2.88/1.49  Total                : 0.69
% 2.88/1.49  Index Insertion      : 0.00
% 2.88/1.49  Index Deletion       : 0.00
% 2.88/1.49  Index Matching       : 0.00
% 2.88/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
