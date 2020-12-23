%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:48 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  150 (1555 expanded)
%              Number of leaves         :   29 ( 618 expanded)
%              Depth                    :   25
%              Number of atoms          :  518 (7515 expanded)
%              Number of equality atoms :   88 ( 416 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m1_orders_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
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
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_91,plain,(
    ! [C_78,A_79,B_80] :
      ( m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_orders_2(C_78,A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_93,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_96,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_93])).

tff(c_97,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_96])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [A_8] :
      ( m1_subset_1(A_8,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_8,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_97,c_14])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_387,plain,(
    ! [A_122,B_123,C_124] :
      ( r2_hidden('#skF_2'(A_122,B_123,C_124),B_123)
      | ~ m1_orders_2(C_124,A_122,B_123)
      | k1_xboole_0 = B_123
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_391,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_2'('#skF_3',B_123,'#skF_5'),B_123)
      | ~ m1_orders_2('#skF_5','#skF_3',B_123)
      | k1_xboole_0 = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_387])).

tff(c_400,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_2'('#skF_3',B_123,'#skF_5'),B_123)
      | ~ m1_orders_2('#skF_5','#skF_3',B_123)
      | k1_xboole_0 = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_391])).

tff(c_443,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_2'('#skF_3',B_134,'#skF_5'),B_134)
      | ~ m1_orders_2('#skF_5','#skF_3',B_134)
      | k1_xboole_0 = B_134
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_400])).

tff(c_449,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_443])).

tff(c_454,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_449])).

tff(c_455,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_454])).

tff(c_125,plain,(
    ! [A_88,B_89,C_90] :
      ( r2_hidden('#skF_2'(A_88,B_89,C_90),B_89)
      | ~ m1_orders_2(C_90,A_88,B_89)
      | k1_xboole_0 = B_89
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_127,plain,(
    ! [B_89] :
      ( r2_hidden('#skF_2'('#skF_3',B_89,'#skF_5'),B_89)
      | ~ m1_orders_2('#skF_5','#skF_3',B_89)
      | k1_xboole_0 = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_125])).

tff(c_132,plain,(
    ! [B_89] :
      ( r2_hidden('#skF_2'('#skF_3',B_89,'#skF_5'),B_89)
      | ~ m1_orders_2('#skF_5','#skF_3',B_89)
      | k1_xboole_0 = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_127])).

tff(c_147,plain,(
    ! [B_92] :
      ( r2_hidden('#skF_2'('#skF_3',B_92,'#skF_5'),B_92)
      | ~ m1_orders_2('#skF_5','#skF_3',B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_132])).

tff(c_151,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_147])).

tff(c_155,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_151])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_102,plain,(
    ! [C_82,A_83] :
      ( k1_xboole_0 = C_82
      | ~ m1_orders_2(C_82,A_83,k1_xboole_0)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_106,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_102])).

tff(c_113,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_106])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_113])).

tff(c_115,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_160,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_115])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_160])).

tff(c_167,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_26,plain,(
    ! [A_11,B_23,C_29] :
      ( m1_subset_1('#skF_2'(A_11,B_23,C_29),u1_struct_0(A_11))
      | ~ m1_orders_2(C_29,A_11,B_23)
      | k1_xboole_0 = B_23
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_198,plain,(
    ! [A_103,B_104,C_105] :
      ( k3_orders_2(A_103,B_104,'#skF_2'(A_103,B_104,C_105)) = C_105
      | ~ m1_orders_2(C_105,A_103,B_104)
      | k1_xboole_0 = B_104
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_200,plain,(
    ! [B_104] :
      ( k3_orders_2('#skF_3',B_104,'#skF_2'('#skF_3',B_104,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_104)
      | k1_xboole_0 = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_198])).

tff(c_205,plain,(
    ! [B_104] :
      ( k3_orders_2('#skF_3',B_104,'#skF_2'('#skF_3',B_104,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_104)
      | k1_xboole_0 = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_200])).

tff(c_232,plain,(
    ! [B_111] :
      ( k3_orders_2('#skF_3',B_111,'#skF_2'('#skF_3',B_111,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_205])).

tff(c_236,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_232])).

tff(c_240,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_236])).

tff(c_241,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_240])).

tff(c_32,plain,(
    ! [B_45,D_51,A_37,C_49] :
      ( r2_hidden(B_45,D_51)
      | ~ r2_hidden(B_45,k3_orders_2(A_37,D_51,C_49))
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(C_49,u1_struct_0(A_37))
      | ~ m1_subset_1(B_45,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | ~ v5_orders_2(A_37)
      | ~ v4_orders_2(A_37)
      | ~ v3_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_246,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_32])).

tff(c_253,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_246])).

tff(c_254,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_253])).

tff(c_256,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_283,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_256])).

tff(c_292,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_97,c_38,c_283])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_167,c_292])).

tff(c_297,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,'#skF_4')
      | ~ r2_hidden(B_114,'#skF_5')
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_319,plain,(
    ! [A_115] :
      ( r2_hidden(A_115,'#skF_4')
      | ~ r2_hidden(A_115,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_297])).

tff(c_336,plain,(
    ! [B_116] :
      ( r2_hidden('#skF_1'('#skF_5',B_116),'#skF_4')
      | r1_tarski('#skF_5',B_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_319])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_342,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_336,c_4])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_342])).

tff(c_349,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_104,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_102])).

tff(c_109,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_104])).

tff(c_110,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_109])).

tff(c_384,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_110])).

tff(c_385,plain,(
    ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_464,plain,(
    ~ m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_385])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_464])).

tff(c_474,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_495,plain,(
    ! [A_138,B_139,C_140] :
      ( k3_orders_2(A_138,B_139,'#skF_2'(A_138,B_139,C_140)) = C_140
      | ~ m1_orders_2(C_140,A_138,B_139)
      | k1_xboole_0 = B_139
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_499,plain,(
    ! [B_139] :
      ( k3_orders_2('#skF_3',B_139,'#skF_2'('#skF_3',B_139,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_139)
      | k1_xboole_0 = B_139
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_495])).

tff(c_508,plain,(
    ! [B_139] :
      ( k3_orders_2('#skF_3',B_139,'#skF_2'('#skF_3',B_139,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_139)
      | k1_xboole_0 = B_139
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_499])).

tff(c_539,plain,(
    ! [B_143] :
      ( k3_orders_2('#skF_3',B_143,'#skF_2'('#skF_3',B_143,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_143)
      | k1_xboole_0 = B_143
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_508])).

tff(c_545,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_539])).

tff(c_550,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_545])).

tff(c_551,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_550])).

tff(c_556,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_32])).

tff(c_563,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_556])).

tff(c_564,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_563])).

tff(c_566,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_569,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_566])).

tff(c_581,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_97,c_38,c_569])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_474,c_581])).

tff(c_586,plain,(
    ! [B_144] :
      ( r2_hidden(B_144,'#skF_4')
      | ~ r2_hidden(B_144,'#skF_5')
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_612,plain,(
    ! [A_145] :
      ( r2_hidden(A_145,'#skF_4')
      | ~ r2_hidden(A_145,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_586])).

tff(c_648,plain,(
    ! [B_150] :
      ( r2_hidden('#skF_1'('#skF_5',B_150),'#skF_4')
      | r1_tarski('#skF_5',B_150) ) ),
    inference(resolution,[status(thm)],[c_6,c_612])).

tff(c_654,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_648,c_4])).

tff(c_659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_654])).

tff(c_660,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_24,plain,(
    ! [A_11,B_23,C_29] :
      ( r2_hidden('#skF_2'(A_11,B_23,C_29),B_23)
      | ~ m1_orders_2(C_29,A_11,B_23)
      | k1_xboole_0 = B_23
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_703,plain,(
    ! [A_154,B_155,C_156] :
      ( r2_hidden('#skF_2'(A_154,B_155,C_156),B_155)
      | ~ m1_orders_2(C_156,A_154,B_155)
      | B_155 = '#skF_5'
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_orders_2(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v4_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | v2_struct_0(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_24])).

tff(c_705,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_2'('#skF_3',B_155,'#skF_5'),B_155)
      | ~ m1_orders_2('#skF_5','#skF_3',B_155)
      | B_155 = '#skF_5'
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_703])).

tff(c_710,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_2'('#skF_3',B_155,'#skF_5'),B_155)
      | ~ m1_orders_2('#skF_5','#skF_3',B_155)
      | B_155 = '#skF_5'
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_705])).

tff(c_725,plain,(
    ! [B_161] :
      ( r2_hidden('#skF_2'('#skF_3',B_161,'#skF_5'),B_161)
      | ~ m1_orders_2('#skF_5','#skF_3',B_161)
      | B_161 = '#skF_5'
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_710])).

tff(c_729,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_725])).

tff(c_736,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_729])).

tff(c_737,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_748,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_36])).

tff(c_752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_748])).

tff(c_754,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_779,plain,(
    ! [A_11,B_23,C_29] :
      ( m1_subset_1('#skF_2'(A_11,B_23,C_29),u1_struct_0(A_11))
      | ~ m1_orders_2(C_29,A_11,B_23)
      | B_23 = '#skF_5'
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_26])).

tff(c_22,plain,(
    ! [A_11,B_23,C_29] :
      ( k3_orders_2(A_11,B_23,'#skF_2'(A_11,B_23,C_29)) = C_29
      | ~ m1_orders_2(C_29,A_11,B_23)
      | k1_xboole_0 = B_23
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_786,plain,(
    ! [A_169,B_170,C_171] :
      ( k3_orders_2(A_169,B_170,'#skF_2'(A_169,B_170,C_171)) = C_171
      | ~ m1_orders_2(C_171,A_169,B_170)
      | B_170 = '#skF_5'
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_orders_2(A_169)
      | ~ v5_orders_2(A_169)
      | ~ v4_orders_2(A_169)
      | ~ v3_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_22])).

tff(c_788,plain,(
    ! [B_170] :
      ( k3_orders_2('#skF_3',B_170,'#skF_2'('#skF_3',B_170,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_170)
      | B_170 = '#skF_5'
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_786])).

tff(c_793,plain,(
    ! [B_170] :
      ( k3_orders_2('#skF_3',B_170,'#skF_2'('#skF_3',B_170,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_170)
      | B_170 = '#skF_5'
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_788])).

tff(c_799,plain,(
    ! [B_172] :
      ( k3_orders_2('#skF_3',B_172,'#skF_2'('#skF_3',B_172,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_172)
      | B_172 = '#skF_5'
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_793])).

tff(c_803,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_799])).

tff(c_810,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_803])).

tff(c_811,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_754,c_810])).

tff(c_824,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_32])).

tff(c_831,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_824])).

tff(c_832,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_831])).

tff(c_834,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_832])).

tff(c_837,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_779,c_834])).

tff(c_846,plain,
    ( '#skF_5' = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_97,c_38,c_837])).

tff(c_848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_754,c_846])).

tff(c_851,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,'#skF_4')
      | ~ r2_hidden(B_174,'#skF_5')
      | ~ m1_subset_1(B_174,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_886,plain,(
    ! [A_179] :
      ( r2_hidden(A_179,'#skF_4')
      | ~ r2_hidden(A_179,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_851])).

tff(c_903,plain,(
    ! [B_180] :
      ( r2_hidden('#skF_1'('#skF_5',B_180),'#skF_4')
      | r1_tarski('#skF_5',B_180) ) ),
    inference(resolution,[status(thm)],[c_6,c_886])).

tff(c_909,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_903,c_4])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.52  
% 3.46/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.53  %$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.46/1.53  
% 3.46/1.53  %Foreground sorts:
% 3.46/1.53  
% 3.46/1.53  
% 3.46/1.53  %Background operators:
% 3.46/1.53  
% 3.46/1.53  
% 3.46/1.53  %Foreground operators:
% 3.46/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.46/1.53  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.46/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.53  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.46/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.46/1.53  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.46/1.53  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.46/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.53  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.46/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.53  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.46/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.53  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.46/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.46/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.46/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.53  
% 3.53/1.55  tff(f_143, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.53/1.55  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.53/1.55  tff(f_97, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_orders_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 3.53/1.55  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.53/1.55  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.55  tff(f_79, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 3.53/1.55  tff(f_123, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.53/1.55  tff(c_36, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.53/1.55  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.55  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.53/1.55  tff(c_48, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.53/1.55  tff(c_46, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.53/1.55  tff(c_44, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.53/1.55  tff(c_42, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.53/1.55  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.53/1.55  tff(c_38, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.53/1.55  tff(c_91, plain, (![C_78, A_79, B_80]: (m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_orders_2(C_78, A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.53/1.55  tff(c_93, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_91])).
% 3.53/1.55  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_93])).
% 3.53/1.55  tff(c_97, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_96])).
% 3.53/1.55  tff(c_14, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.53/1.55  tff(c_100, plain, (![A_8]: (m1_subset_1(A_8, u1_struct_0('#skF_3')) | ~r2_hidden(A_8, '#skF_5'))), inference(resolution, [status(thm)], [c_97, c_14])).
% 3.53/1.55  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.55  tff(c_387, plain, (![A_122, B_123, C_124]: (r2_hidden('#skF_2'(A_122, B_123, C_124), B_123) | ~m1_orders_2(C_124, A_122, B_123) | k1_xboole_0=B_123 | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.55  tff(c_391, plain, (![B_123]: (r2_hidden('#skF_2'('#skF_3', B_123, '#skF_5'), B_123) | ~m1_orders_2('#skF_5', '#skF_3', B_123) | k1_xboole_0=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_387])).
% 3.53/1.55  tff(c_400, plain, (![B_123]: (r2_hidden('#skF_2'('#skF_3', B_123, '#skF_5'), B_123) | ~m1_orders_2('#skF_5', '#skF_3', B_123) | k1_xboole_0=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_391])).
% 3.53/1.55  tff(c_443, plain, (![B_134]: (r2_hidden('#skF_2'('#skF_3', B_134, '#skF_5'), B_134) | ~m1_orders_2('#skF_5', '#skF_3', B_134) | k1_xboole_0=B_134 | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_400])).
% 3.53/1.55  tff(c_449, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_443])).
% 3.53/1.55  tff(c_454, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_449])).
% 3.53/1.55  tff(c_455, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_454])).
% 3.53/1.55  tff(c_125, plain, (![A_88, B_89, C_90]: (r2_hidden('#skF_2'(A_88, B_89, C_90), B_89) | ~m1_orders_2(C_90, A_88, B_89) | k1_xboole_0=B_89 | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.55  tff(c_127, plain, (![B_89]: (r2_hidden('#skF_2'('#skF_3', B_89, '#skF_5'), B_89) | ~m1_orders_2('#skF_5', '#skF_3', B_89) | k1_xboole_0=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_125])).
% 3.53/1.55  tff(c_132, plain, (![B_89]: (r2_hidden('#skF_2'('#skF_3', B_89, '#skF_5'), B_89) | ~m1_orders_2('#skF_5', '#skF_3', B_89) | k1_xboole_0=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_127])).
% 3.53/1.55  tff(c_147, plain, (![B_92]: (r2_hidden('#skF_2'('#skF_3', B_92, '#skF_5'), B_92) | ~m1_orders_2('#skF_5', '#skF_3', B_92) | k1_xboole_0=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_132])).
% 3.53/1.55  tff(c_151, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_147])).
% 3.53/1.55  tff(c_155, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_151])).
% 3.53/1.55  tff(c_156, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_155])).
% 3.53/1.55  tff(c_102, plain, (![C_82, A_83]: (k1_xboole_0=C_82 | ~m1_orders_2(C_82, A_83, k1_xboole_0) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.55  tff(c_106, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_102])).
% 3.53/1.55  tff(c_113, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_106])).
% 3.53/1.55  tff(c_114, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_113])).
% 3.53/1.55  tff(c_115, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_114])).
% 3.53/1.55  tff(c_160, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_115])).
% 3.53/1.55  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_160])).
% 3.53/1.55  tff(c_167, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_155])).
% 3.53/1.55  tff(c_26, plain, (![A_11, B_23, C_29]: (m1_subset_1('#skF_2'(A_11, B_23, C_29), u1_struct_0(A_11)) | ~m1_orders_2(C_29, A_11, B_23) | k1_xboole_0=B_23 | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.55  tff(c_198, plain, (![A_103, B_104, C_105]: (k3_orders_2(A_103, B_104, '#skF_2'(A_103, B_104, C_105))=C_105 | ~m1_orders_2(C_105, A_103, B_104) | k1_xboole_0=B_104 | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.55  tff(c_200, plain, (![B_104]: (k3_orders_2('#skF_3', B_104, '#skF_2'('#skF_3', B_104, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_104) | k1_xboole_0=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_198])).
% 3.53/1.55  tff(c_205, plain, (![B_104]: (k3_orders_2('#skF_3', B_104, '#skF_2'('#skF_3', B_104, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_104) | k1_xboole_0=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_200])).
% 3.53/1.55  tff(c_232, plain, (![B_111]: (k3_orders_2('#skF_3', B_111, '#skF_2'('#skF_3', B_111, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_205])).
% 3.53/1.55  tff(c_236, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_232])).
% 3.53/1.55  tff(c_240, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_236])).
% 3.53/1.55  tff(c_241, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_167, c_240])).
% 3.53/1.55  tff(c_32, plain, (![B_45, D_51, A_37, C_49]: (r2_hidden(B_45, D_51) | ~r2_hidden(B_45, k3_orders_2(A_37, D_51, C_49)) | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(C_49, u1_struct_0(A_37)) | ~m1_subset_1(B_45, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | ~v5_orders_2(A_37) | ~v4_orders_2(A_37) | ~v3_orders_2(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.53/1.55  tff(c_246, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_32])).
% 3.53/1.55  tff(c_253, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_246])).
% 3.53/1.55  tff(c_254, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_253])).
% 3.53/1.55  tff(c_256, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_254])).
% 3.53/1.55  tff(c_283, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_256])).
% 3.53/1.55  tff(c_292, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_97, c_38, c_283])).
% 3.53/1.55  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_167, c_292])).
% 3.53/1.55  tff(c_297, plain, (![B_114]: (r2_hidden(B_114, '#skF_4') | ~r2_hidden(B_114, '#skF_5') | ~m1_subset_1(B_114, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_254])).
% 3.53/1.55  tff(c_319, plain, (![A_115]: (r2_hidden(A_115, '#skF_4') | ~r2_hidden(A_115, '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_297])).
% 3.53/1.55  tff(c_336, plain, (![B_116]: (r2_hidden('#skF_1'('#skF_5', B_116), '#skF_4') | r1_tarski('#skF_5', B_116))), inference(resolution, [status(thm)], [c_6, c_319])).
% 3.53/1.55  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.55  tff(c_342, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_336, c_4])).
% 3.53/1.55  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_342])).
% 3.53/1.55  tff(c_349, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_114])).
% 3.53/1.55  tff(c_104, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_97, c_102])).
% 3.53/1.55  tff(c_109, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_104])).
% 3.53/1.55  tff(c_110, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_109])).
% 3.53/1.55  tff(c_384, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_349, c_110])).
% 3.53/1.55  tff(c_385, plain, (~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_384])).
% 3.53/1.55  tff(c_464, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_455, c_385])).
% 3.53/1.55  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_464])).
% 3.53/1.55  tff(c_474, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_454])).
% 3.53/1.55  tff(c_495, plain, (![A_138, B_139, C_140]: (k3_orders_2(A_138, B_139, '#skF_2'(A_138, B_139, C_140))=C_140 | ~m1_orders_2(C_140, A_138, B_139) | k1_xboole_0=B_139 | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.55  tff(c_499, plain, (![B_139]: (k3_orders_2('#skF_3', B_139, '#skF_2'('#skF_3', B_139, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_139) | k1_xboole_0=B_139 | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_495])).
% 3.53/1.55  tff(c_508, plain, (![B_139]: (k3_orders_2('#skF_3', B_139, '#skF_2'('#skF_3', B_139, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_139) | k1_xboole_0=B_139 | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_499])).
% 3.53/1.55  tff(c_539, plain, (![B_143]: (k3_orders_2('#skF_3', B_143, '#skF_2'('#skF_3', B_143, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_143) | k1_xboole_0=B_143 | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_508])).
% 3.53/1.55  tff(c_545, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_539])).
% 3.53/1.55  tff(c_550, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_545])).
% 3.53/1.55  tff(c_551, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_474, c_550])).
% 3.53/1.55  tff(c_556, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_551, c_32])).
% 3.53/1.55  tff(c_563, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_556])).
% 3.53/1.55  tff(c_564, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_563])).
% 3.53/1.55  tff(c_566, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_564])).
% 3.53/1.55  tff(c_569, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_566])).
% 3.53/1.55  tff(c_581, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_97, c_38, c_569])).
% 3.53/1.55  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_474, c_581])).
% 3.53/1.55  tff(c_586, plain, (![B_144]: (r2_hidden(B_144, '#skF_4') | ~r2_hidden(B_144, '#skF_5') | ~m1_subset_1(B_144, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_564])).
% 3.53/1.55  tff(c_612, plain, (![A_145]: (r2_hidden(A_145, '#skF_4') | ~r2_hidden(A_145, '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_586])).
% 3.53/1.55  tff(c_648, plain, (![B_150]: (r2_hidden('#skF_1'('#skF_5', B_150), '#skF_4') | r1_tarski('#skF_5', B_150))), inference(resolution, [status(thm)], [c_6, c_612])).
% 3.53/1.55  tff(c_654, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_648, c_4])).
% 3.53/1.55  tff(c_659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_654])).
% 3.53/1.55  tff(c_660, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_384])).
% 3.53/1.55  tff(c_24, plain, (![A_11, B_23, C_29]: (r2_hidden('#skF_2'(A_11, B_23, C_29), B_23) | ~m1_orders_2(C_29, A_11, B_23) | k1_xboole_0=B_23 | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.55  tff(c_703, plain, (![A_154, B_155, C_156]: (r2_hidden('#skF_2'(A_154, B_155, C_156), B_155) | ~m1_orders_2(C_156, A_154, B_155) | B_155='#skF_5' | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_orders_2(A_154) | ~v5_orders_2(A_154) | ~v4_orders_2(A_154) | ~v3_orders_2(A_154) | v2_struct_0(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_660, c_24])).
% 3.53/1.55  tff(c_705, plain, (![B_155]: (r2_hidden('#skF_2'('#skF_3', B_155, '#skF_5'), B_155) | ~m1_orders_2('#skF_5', '#skF_3', B_155) | B_155='#skF_5' | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_703])).
% 3.53/1.55  tff(c_710, plain, (![B_155]: (r2_hidden('#skF_2'('#skF_3', B_155, '#skF_5'), B_155) | ~m1_orders_2('#skF_5', '#skF_3', B_155) | B_155='#skF_5' | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_705])).
% 3.53/1.55  tff(c_725, plain, (![B_161]: (r2_hidden('#skF_2'('#skF_3', B_161, '#skF_5'), B_161) | ~m1_orders_2('#skF_5', '#skF_3', B_161) | B_161='#skF_5' | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_710])).
% 3.53/1.55  tff(c_729, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_725])).
% 3.53/1.55  tff(c_736, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_729])).
% 3.53/1.55  tff(c_737, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_736])).
% 3.53/1.55  tff(c_748, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_36])).
% 3.53/1.55  tff(c_752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_748])).
% 3.53/1.55  tff(c_754, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_736])).
% 3.53/1.55  tff(c_779, plain, (![A_11, B_23, C_29]: (m1_subset_1('#skF_2'(A_11, B_23, C_29), u1_struct_0(A_11)) | ~m1_orders_2(C_29, A_11, B_23) | B_23='#skF_5' | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_660, c_26])).
% 3.53/1.55  tff(c_22, plain, (![A_11, B_23, C_29]: (k3_orders_2(A_11, B_23, '#skF_2'(A_11, B_23, C_29))=C_29 | ~m1_orders_2(C_29, A_11, B_23) | k1_xboole_0=B_23 | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.55  tff(c_786, plain, (![A_169, B_170, C_171]: (k3_orders_2(A_169, B_170, '#skF_2'(A_169, B_170, C_171))=C_171 | ~m1_orders_2(C_171, A_169, B_170) | B_170='#skF_5' | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(A_169))) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_orders_2(A_169) | ~v5_orders_2(A_169) | ~v4_orders_2(A_169) | ~v3_orders_2(A_169) | v2_struct_0(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_660, c_22])).
% 3.53/1.55  tff(c_788, plain, (![B_170]: (k3_orders_2('#skF_3', B_170, '#skF_2'('#skF_3', B_170, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_170) | B_170='#skF_5' | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_786])).
% 3.53/1.55  tff(c_793, plain, (![B_170]: (k3_orders_2('#skF_3', B_170, '#skF_2'('#skF_3', B_170, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_170) | B_170='#skF_5' | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_788])).
% 3.53/1.55  tff(c_799, plain, (![B_172]: (k3_orders_2('#skF_3', B_172, '#skF_2'('#skF_3', B_172, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_172) | B_172='#skF_5' | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_793])).
% 3.53/1.55  tff(c_803, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_799])).
% 3.53/1.55  tff(c_810, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_803])).
% 3.53/1.55  tff(c_811, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_754, c_810])).
% 3.53/1.55  tff(c_824, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_811, c_32])).
% 3.53/1.55  tff(c_831, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_824])).
% 3.53/1.55  tff(c_832, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_831])).
% 3.53/1.55  tff(c_834, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_832])).
% 3.53/1.55  tff(c_837, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_779, c_834])).
% 3.53/1.55  tff(c_846, plain, ('#skF_5'='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_97, c_38, c_837])).
% 3.53/1.55  tff(c_848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_754, c_846])).
% 3.53/1.55  tff(c_851, plain, (![B_174]: (r2_hidden(B_174, '#skF_4') | ~r2_hidden(B_174, '#skF_5') | ~m1_subset_1(B_174, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_832])).
% 3.53/1.55  tff(c_886, plain, (![A_179]: (r2_hidden(A_179, '#skF_4') | ~r2_hidden(A_179, '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_851])).
% 3.53/1.55  tff(c_903, plain, (![B_180]: (r2_hidden('#skF_1'('#skF_5', B_180), '#skF_4') | r1_tarski('#skF_5', B_180))), inference(resolution, [status(thm)], [c_6, c_886])).
% 3.53/1.55  tff(c_909, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_903, c_4])).
% 3.53/1.55  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_909])).
% 3.53/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.55  
% 3.53/1.55  Inference rules
% 3.53/1.55  ----------------------
% 3.53/1.55  #Ref     : 0
% 3.53/1.55  #Sup     : 156
% 3.53/1.55  #Fact    : 0
% 3.53/1.55  #Define  : 0
% 3.53/1.55  #Split   : 18
% 3.53/1.55  #Chain   : 0
% 3.53/1.55  #Close   : 0
% 3.53/1.55  
% 3.53/1.55  Ordering : KBO
% 3.53/1.55  
% 3.53/1.55  Simplification rules
% 3.53/1.55  ----------------------
% 3.53/1.55  #Subsume      : 29
% 3.53/1.55  #Demod        : 297
% 3.53/1.55  #Tautology    : 35
% 3.53/1.55  #SimpNegUnit  : 56
% 3.53/1.55  #BackRed      : 35
% 3.53/1.55  
% 3.53/1.55  #Partial instantiations: 0
% 3.53/1.55  #Strategies tried      : 1
% 3.53/1.55  
% 3.53/1.55  Timing (in seconds)
% 3.53/1.55  ----------------------
% 3.53/1.56  Preprocessing        : 0.32
% 3.53/1.56  Parsing              : 0.17
% 3.53/1.56  CNF conversion       : 0.03
% 3.53/1.56  Main loop            : 0.44
% 3.53/1.56  Inferencing          : 0.16
% 3.53/1.56  Reduction            : 0.14
% 3.53/1.56  Demodulation         : 0.10
% 3.53/1.56  BG Simplification    : 0.02
% 3.53/1.56  Subsumption          : 0.10
% 3.53/1.56  Abstraction          : 0.02
% 3.53/1.56  MUC search           : 0.00
% 3.53/1.56  Cooper               : 0.00
% 3.53/1.56  Total                : 0.82
% 3.53/1.56  Index Insertion      : 0.00
% 3.53/1.56  Index Deletion       : 0.00
% 3.53/1.56  Index Matching       : 0.00
% 3.53/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
