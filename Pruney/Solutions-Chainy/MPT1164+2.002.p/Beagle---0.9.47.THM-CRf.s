%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:48 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 888 expanded)
%              Number of leaves         :   29 ( 360 expanded)
%              Depth                    :   19
%              Number of atoms          :  378 (4186 expanded)
%              Number of equality atoms :   60 ( 213 expanded)
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

tff(f_139,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_32,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_91,plain,(
    ! [C_79,A_80,B_81] :
      ( m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_orders_2(C_79,A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_93,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_91])).

tff(c_96,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_93])).

tff(c_97,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_96])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_100,plain,(
    ! [A_7] :
      ( m1_subset_1(A_7,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_7,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_97,c_10])).

tff(c_416,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_hidden('#skF_2'(A_127,B_128,C_129),B_128)
      | ~ m1_orders_2(C_129,A_127,B_128)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_420,plain,(
    ! [B_128] :
      ( r2_hidden('#skF_2'('#skF_3',B_128,'#skF_5'),B_128)
      | ~ m1_orders_2('#skF_5','#skF_3',B_128)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_416])).

tff(c_429,plain,(
    ! [B_128] :
      ( r2_hidden('#skF_2'('#skF_3',B_128,'#skF_5'),B_128)
      | ~ m1_orders_2('#skF_5','#skF_3',B_128)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_420])).

tff(c_463,plain,(
    ! [B_135] :
      ( r2_hidden('#skF_2'('#skF_3',B_135,'#skF_5'),B_135)
      | ~ m1_orders_2('#skF_5','#skF_3',B_135)
      | k1_xboole_0 = B_135
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_429])).

tff(c_469,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_463])).

tff(c_474,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_469])).

tff(c_484,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_127,plain,(
    ! [A_87,B_88,C_89] :
      ( r2_hidden('#skF_2'(A_87,B_88,C_89),B_88)
      | ~ m1_orders_2(C_89,A_87,B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_129,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_2'('#skF_3',B_88,'#skF_5'),B_88)
      | ~ m1_orders_2('#skF_5','#skF_3',B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_127])).

tff(c_134,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_2'('#skF_3',B_88,'#skF_5'),B_88)
      | ~ m1_orders_2('#skF_5','#skF_3',B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_129])).

tff(c_149,plain,(
    ! [B_91] :
      ( r2_hidden('#skF_2'('#skF_3',B_91,'#skF_5'),B_91)
      | ~ m1_orders_2('#skF_5','#skF_3',B_91)
      | k1_xboole_0 = B_91
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_134])).

tff(c_153,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_149])).

tff(c_157,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_153])).

tff(c_158,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_113,plain,(
    ! [C_85,A_86] :
      ( k1_xboole_0 = C_85
      | ~ m1_orders_2(C_85,A_86,k1_xboole_0)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_113])).

tff(c_124,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_117])).

tff(c_125,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_124])).

tff(c_126,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_170,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_126])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_170])).

tff(c_180,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_22,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_2'(A_10,B_22,C_28),u1_struct_0(A_10))
      | ~ m1_orders_2(C_28,A_10,B_22)
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10)
      | ~ v5_orders_2(A_10)
      | ~ v4_orders_2(A_10)
      | ~ v3_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_224,plain,(
    ! [A_110,B_111,C_112] :
      ( k3_orders_2(A_110,B_111,'#skF_2'(A_110,B_111,C_112)) = C_112
      | ~ m1_orders_2(C_112,A_110,B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_226,plain,(
    ! [B_111] :
      ( k3_orders_2('#skF_3',B_111,'#skF_2'('#skF_3',B_111,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_224])).

tff(c_231,plain,(
    ! [B_111] :
      ( k3_orders_2('#skF_3',B_111,'#skF_2'('#skF_3',B_111,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_226])).

tff(c_245,plain,(
    ! [B_114] :
      ( k3_orders_2('#skF_3',B_114,'#skF_2'('#skF_3',B_114,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_231])).

tff(c_249,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_245])).

tff(c_253,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_249])).

tff(c_254,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_253])).

tff(c_28,plain,(
    ! [B_44,D_50,A_36,C_48] :
      ( r2_hidden(B_44,D_50)
      | ~ r2_hidden(B_44,k3_orders_2(A_36,D_50,C_48))
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(C_48,u1_struct_0(A_36))
      | ~ m1_subset_1(B_44,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36)
      | ~ v5_orders_2(A_36)
      | ~ v4_orders_2(A_36)
      | ~ v3_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_259,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_4')
      | ~ r2_hidden(B_44,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_28])).

tff(c_266,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_4')
      | ~ r2_hidden(B_44,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_259])).

tff(c_267,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_4')
      | ~ r2_hidden(B_44,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_266])).

tff(c_269,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_272,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_269])).

tff(c_281,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_97,c_34,c_272])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_180,c_281])).

tff(c_299,plain,(
    ! [B_119] :
      ( r2_hidden(B_119,'#skF_4')
      | ~ r2_hidden(B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_321,plain,(
    ! [A_120] :
      ( r2_hidden(A_120,'#skF_4')
      | ~ r2_hidden(A_120,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_299])).

tff(c_338,plain,(
    ! [B_121] :
      ( r2_hidden('#skF_1'('#skF_5',B_121),'#skF_4')
      | r1_tarski('#skF_5',B_121) ) ),
    inference(resolution,[status(thm)],[c_6,c_321])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_344,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_4])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_344])).

tff(c_351,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_115,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_113])).

tff(c_120,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_115])).

tff(c_121,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_120])).

tff(c_352,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_352])).

tff(c_378,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_414,plain,(
    ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_493,plain,(
    ~ m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_414])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_493])).

tff(c_505,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_530,plain,(
    ! [A_143,B_144,C_145] :
      ( k3_orders_2(A_143,B_144,'#skF_2'(A_143,B_144,C_145)) = C_145
      | ~ m1_orders_2(C_145,A_143,B_144)
      | k1_xboole_0 = B_144
      | ~ m1_subset_1(C_145,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_orders_2(A_143)
      | ~ v5_orders_2(A_143)
      | ~ v4_orders_2(A_143)
      | ~ v3_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_534,plain,(
    ! [B_144] :
      ( k3_orders_2('#skF_3',B_144,'#skF_2'('#skF_3',B_144,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_144)
      | k1_xboole_0 = B_144
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_530])).

tff(c_543,plain,(
    ! [B_144] :
      ( k3_orders_2('#skF_3',B_144,'#skF_2'('#skF_3',B_144,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_144)
      | k1_xboole_0 = B_144
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_534])).

tff(c_574,plain,(
    ! [B_148] :
      ( k3_orders_2('#skF_3',B_148,'#skF_2'('#skF_3',B_148,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_148)
      | k1_xboole_0 = B_148
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_543])).

tff(c_580,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_574])).

tff(c_585,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_580])).

tff(c_586,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_585])).

tff(c_591,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_4')
      | ~ r2_hidden(B_44,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_28])).

tff(c_598,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_4')
      | ~ r2_hidden(B_44,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_591])).

tff(c_599,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_4')
      | ~ r2_hidden(B_44,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_598])).

tff(c_601,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_599])).

tff(c_604,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_601])).

tff(c_616,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_97,c_34,c_604])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_505,c_616])).

tff(c_621,plain,(
    ! [B_149] :
      ( r2_hidden(B_149,'#skF_4')
      | ~ r2_hidden(B_149,'#skF_5')
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_599])).

tff(c_666,plain,(
    ! [A_154] :
      ( r2_hidden(A_154,'#skF_4')
      | ~ r2_hidden(A_154,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_621])).

tff(c_683,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_1'('#skF_5',B_155),'#skF_4')
      | r1_tarski('#skF_5',B_155) ) ),
    inference(resolution,[status(thm)],[c_6,c_666])).

tff(c_689,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_683,c_4])).

tff(c_694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_689])).

tff(c_695,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_703,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_8])).

tff(c_717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  
% 3.06/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  %$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.06/1.48  
% 3.06/1.48  %Foreground sorts:
% 3.06/1.48  
% 3.06/1.48  
% 3.06/1.48  %Background operators:
% 3.06/1.48  
% 3.06/1.48  
% 3.06/1.48  %Foreground operators:
% 3.06/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.48  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.48  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.06/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.06/1.48  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.06/1.48  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.06/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.48  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.06/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.48  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.06/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.48  
% 3.23/1.51  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 3.23/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.51  tff(f_93, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_orders_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 3.23/1.51  tff(f_40, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.23/1.51  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 3.23/1.51  tff(f_119, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.23/1.51  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.51  tff(c_32, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.51  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_44, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_42, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_40, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_38, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_34, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.23/1.51  tff(c_91, plain, (![C_79, A_80, B_81]: (m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_orders_2(C_79, A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.23/1.51  tff(c_93, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_91])).
% 3.23/1.51  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_93])).
% 3.23/1.51  tff(c_97, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_96])).
% 3.23/1.51  tff(c_10, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.51  tff(c_100, plain, (![A_7]: (m1_subset_1(A_7, u1_struct_0('#skF_3')) | ~r2_hidden(A_7, '#skF_5'))), inference(resolution, [status(thm)], [c_97, c_10])).
% 3.23/1.51  tff(c_416, plain, (![A_127, B_128, C_129]: (r2_hidden('#skF_2'(A_127, B_128, C_129), B_128) | ~m1_orders_2(C_129, A_127, B_128) | k1_xboole_0=B_128 | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.51  tff(c_420, plain, (![B_128]: (r2_hidden('#skF_2'('#skF_3', B_128, '#skF_5'), B_128) | ~m1_orders_2('#skF_5', '#skF_3', B_128) | k1_xboole_0=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_416])).
% 3.23/1.51  tff(c_429, plain, (![B_128]: (r2_hidden('#skF_2'('#skF_3', B_128, '#skF_5'), B_128) | ~m1_orders_2('#skF_5', '#skF_3', B_128) | k1_xboole_0=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_420])).
% 3.23/1.51  tff(c_463, plain, (![B_135]: (r2_hidden('#skF_2'('#skF_3', B_135, '#skF_5'), B_135) | ~m1_orders_2('#skF_5', '#skF_3', B_135) | k1_xboole_0=B_135 | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_429])).
% 3.23/1.51  tff(c_469, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_463])).
% 3.23/1.51  tff(c_474, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_469])).
% 3.23/1.51  tff(c_484, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_474])).
% 3.23/1.51  tff(c_127, plain, (![A_87, B_88, C_89]: (r2_hidden('#skF_2'(A_87, B_88, C_89), B_88) | ~m1_orders_2(C_89, A_87, B_88) | k1_xboole_0=B_88 | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.51  tff(c_129, plain, (![B_88]: (r2_hidden('#skF_2'('#skF_3', B_88, '#skF_5'), B_88) | ~m1_orders_2('#skF_5', '#skF_3', B_88) | k1_xboole_0=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_127])).
% 3.23/1.51  tff(c_134, plain, (![B_88]: (r2_hidden('#skF_2'('#skF_3', B_88, '#skF_5'), B_88) | ~m1_orders_2('#skF_5', '#skF_3', B_88) | k1_xboole_0=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_129])).
% 3.23/1.51  tff(c_149, plain, (![B_91]: (r2_hidden('#skF_2'('#skF_3', B_91, '#skF_5'), B_91) | ~m1_orders_2('#skF_5', '#skF_3', B_91) | k1_xboole_0=B_91 | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_134])).
% 3.23/1.51  tff(c_153, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_149])).
% 3.23/1.51  tff(c_157, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_153])).
% 3.23/1.51  tff(c_158, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_157])).
% 3.23/1.51  tff(c_113, plain, (![C_85, A_86]: (k1_xboole_0=C_85 | ~m1_orders_2(C_85, A_86, k1_xboole_0) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.51  tff(c_117, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_113])).
% 3.23/1.51  tff(c_124, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_117])).
% 3.23/1.51  tff(c_125, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_124])).
% 3.23/1.51  tff(c_126, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_125])).
% 3.23/1.51  tff(c_170, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_126])).
% 3.23/1.51  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_170])).
% 3.23/1.51  tff(c_180, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_157])).
% 3.23/1.51  tff(c_22, plain, (![A_10, B_22, C_28]: (m1_subset_1('#skF_2'(A_10, B_22, C_28), u1_struct_0(A_10)) | ~m1_orders_2(C_28, A_10, B_22) | k1_xboole_0=B_22 | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_orders_2(A_10) | ~v5_orders_2(A_10) | ~v4_orders_2(A_10) | ~v3_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.51  tff(c_224, plain, (![A_110, B_111, C_112]: (k3_orders_2(A_110, B_111, '#skF_2'(A_110, B_111, C_112))=C_112 | ~m1_orders_2(C_112, A_110, B_111) | k1_xboole_0=B_111 | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.51  tff(c_226, plain, (![B_111]: (k3_orders_2('#skF_3', B_111, '#skF_2'('#skF_3', B_111, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_224])).
% 3.23/1.51  tff(c_231, plain, (![B_111]: (k3_orders_2('#skF_3', B_111, '#skF_2'('#skF_3', B_111, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_226])).
% 3.23/1.51  tff(c_245, plain, (![B_114]: (k3_orders_2('#skF_3', B_114, '#skF_2'('#skF_3', B_114, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_114) | k1_xboole_0=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_231])).
% 3.23/1.51  tff(c_249, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_245])).
% 3.23/1.51  tff(c_253, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_249])).
% 3.23/1.51  tff(c_254, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_180, c_253])).
% 3.23/1.51  tff(c_28, plain, (![B_44, D_50, A_36, C_48]: (r2_hidden(B_44, D_50) | ~r2_hidden(B_44, k3_orders_2(A_36, D_50, C_48)) | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(C_48, u1_struct_0(A_36)) | ~m1_subset_1(B_44, u1_struct_0(A_36)) | ~l1_orders_2(A_36) | ~v5_orders_2(A_36) | ~v4_orders_2(A_36) | ~v3_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.23/1.51  tff(c_259, plain, (![B_44]: (r2_hidden(B_44, '#skF_4') | ~r2_hidden(B_44, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_254, c_28])).
% 3.23/1.51  tff(c_266, plain, (![B_44]: (r2_hidden(B_44, '#skF_4') | ~r2_hidden(B_44, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_259])).
% 3.23/1.51  tff(c_267, plain, (![B_44]: (r2_hidden(B_44, '#skF_4') | ~r2_hidden(B_44, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_266])).
% 3.23/1.51  tff(c_269, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_267])).
% 3.23/1.51  tff(c_272, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_269])).
% 3.23/1.51  tff(c_281, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_97, c_34, c_272])).
% 3.23/1.51  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_180, c_281])).
% 3.23/1.51  tff(c_299, plain, (![B_119]: (r2_hidden(B_119, '#skF_4') | ~r2_hidden(B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_267])).
% 3.23/1.51  tff(c_321, plain, (![A_120]: (r2_hidden(A_120, '#skF_4') | ~r2_hidden(A_120, '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_299])).
% 3.23/1.51  tff(c_338, plain, (![B_121]: (r2_hidden('#skF_1'('#skF_5', B_121), '#skF_4') | r1_tarski('#skF_5', B_121))), inference(resolution, [status(thm)], [c_6, c_321])).
% 3.23/1.51  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.51  tff(c_344, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_338, c_4])).
% 3.23/1.51  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_344])).
% 3.23/1.51  tff(c_351, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_125])).
% 3.23/1.51  tff(c_115, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_97, c_113])).
% 3.23/1.51  tff(c_120, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_115])).
% 3.23/1.51  tff(c_121, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_120])).
% 3.23/1.51  tff(c_352, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_121])).
% 3.23/1.51  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_351, c_352])).
% 3.23/1.51  tff(c_378, plain, (~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_121])).
% 3.23/1.51  tff(c_414, plain, (~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_378])).
% 3.23/1.51  tff(c_493, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_414])).
% 3.23/1.51  tff(c_503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_493])).
% 3.23/1.51  tff(c_505, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_474])).
% 3.23/1.51  tff(c_530, plain, (![A_143, B_144, C_145]: (k3_orders_2(A_143, B_144, '#skF_2'(A_143, B_144, C_145))=C_145 | ~m1_orders_2(C_145, A_143, B_144) | k1_xboole_0=B_144 | ~m1_subset_1(C_145, k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_orders_2(A_143) | ~v5_orders_2(A_143) | ~v4_orders_2(A_143) | ~v3_orders_2(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.51  tff(c_534, plain, (![B_144]: (k3_orders_2('#skF_3', B_144, '#skF_2'('#skF_3', B_144, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_144) | k1_xboole_0=B_144 | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_97, c_530])).
% 3.23/1.51  tff(c_543, plain, (![B_144]: (k3_orders_2('#skF_3', B_144, '#skF_2'('#skF_3', B_144, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_144) | k1_xboole_0=B_144 | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_534])).
% 3.23/1.51  tff(c_574, plain, (![B_148]: (k3_orders_2('#skF_3', B_148, '#skF_2'('#skF_3', B_148, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_148) | k1_xboole_0=B_148 | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_543])).
% 3.23/1.51  tff(c_580, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_574])).
% 3.23/1.51  tff(c_585, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_580])).
% 3.23/1.51  tff(c_586, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_505, c_585])).
% 3.23/1.51  tff(c_591, plain, (![B_44]: (r2_hidden(B_44, '#skF_4') | ~r2_hidden(B_44, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_586, c_28])).
% 3.23/1.51  tff(c_598, plain, (![B_44]: (r2_hidden(B_44, '#skF_4') | ~r2_hidden(B_44, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_591])).
% 3.23/1.51  tff(c_599, plain, (![B_44]: (r2_hidden(B_44, '#skF_4') | ~r2_hidden(B_44, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_598])).
% 3.23/1.51  tff(c_601, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_599])).
% 3.23/1.51  tff(c_604, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_601])).
% 3.23/1.51  tff(c_616, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_97, c_34, c_604])).
% 3.23/1.51  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_505, c_616])).
% 3.23/1.51  tff(c_621, plain, (![B_149]: (r2_hidden(B_149, '#skF_4') | ~r2_hidden(B_149, '#skF_5') | ~m1_subset_1(B_149, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_599])).
% 3.23/1.51  tff(c_666, plain, (![A_154]: (r2_hidden(A_154, '#skF_4') | ~r2_hidden(A_154, '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_621])).
% 3.23/1.51  tff(c_683, plain, (![B_155]: (r2_hidden('#skF_1'('#skF_5', B_155), '#skF_4') | r1_tarski('#skF_5', B_155))), inference(resolution, [status(thm)], [c_6, c_666])).
% 3.23/1.51  tff(c_689, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_683, c_4])).
% 3.23/1.51  tff(c_694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_689])).
% 3.23/1.51  tff(c_695, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_378])).
% 3.23/1.51  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.23/1.51  tff(c_703, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_695, c_8])).
% 3.23/1.51  tff(c_717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_703, c_32])).
% 3.23/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  Inference rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Ref     : 0
% 3.23/1.51  #Sup     : 123
% 3.23/1.51  #Fact    : 0
% 3.23/1.51  #Define  : 0
% 3.23/1.51  #Split   : 18
% 3.23/1.51  #Chain   : 0
% 3.23/1.51  #Close   : 0
% 3.23/1.51  
% 3.23/1.51  Ordering : KBO
% 3.23/1.51  
% 3.23/1.51  Simplification rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Subsume      : 23
% 3.23/1.51  #Demod        : 216
% 3.23/1.51  #Tautology    : 24
% 3.23/1.51  #SimpNegUnit  : 40
% 3.23/1.51  #BackRed      : 32
% 3.23/1.51  
% 3.23/1.51  #Partial instantiations: 0
% 3.23/1.51  #Strategies tried      : 1
% 3.23/1.51  
% 3.23/1.51  Timing (in seconds)
% 3.23/1.51  ----------------------
% 3.23/1.51  Preprocessing        : 0.32
% 3.23/1.51  Parsing              : 0.16
% 3.23/1.51  CNF conversion       : 0.03
% 3.23/1.51  Main loop            : 0.39
% 3.23/1.51  Inferencing          : 0.13
% 3.23/1.51  Reduction            : 0.12
% 3.23/1.51  Demodulation         : 0.08
% 3.23/1.51  BG Simplification    : 0.02
% 3.23/1.51  Subsumption          : 0.09
% 3.23/1.51  Abstraction          : 0.02
% 3.23/1.51  MUC search           : 0.00
% 3.23/1.51  Cooper               : 0.00
% 3.23/1.51  Total                : 0.75
% 3.23/1.51  Index Insertion      : 0.00
% 3.23/1.51  Index Deletion       : 0.00
% 3.23/1.51  Index Matching       : 0.00
% 3.23/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
