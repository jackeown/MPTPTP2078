%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:24 EST 2020

% Result     : Theorem 13.35s
% Output     : CNFRefutation 13.50s
% Verified   : 
% Statistics : Number of formulae       :  119 (1032 expanded)
%              Number of leaves         :   41 ( 400 expanded)
%              Depth                    :   22
%              Number of atoms          :  307 (3204 expanded)
%              Number of equality atoms :   37 ( 592 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_73,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_66,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_64,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_62,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_44,plain,(
    ! [A_40] :
      ( l1_struct_0(A_40)
      | ~ l1_orders_2(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_75,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_85,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_orders_2(A_62) ) ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_89,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_85])).

tff(c_356,plain,(
    ! [A_118,B_119] :
      ( k1_orders_2(A_118,B_119) = a_2_0_orders_2(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_367,plain,(
    ! [B_119] :
      ( k1_orders_2('#skF_5',B_119) = a_2_0_orders_2('#skF_5',B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_356])).

tff(c_375,plain,(
    ! [B_119] :
      ( k1_orders_2('#skF_5',B_119) = a_2_0_orders_2('#skF_5',B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_367])).

tff(c_421,plain,(
    ! [B_125] :
      ( k1_orders_2('#skF_5',B_125) = a_2_0_orders_2('#skF_5',B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_375])).

tff(c_441,plain,(
    ! [A_126] :
      ( k1_orders_2('#skF_5',A_126) = a_2_0_orders_2('#skF_5',A_126)
      | ~ r1_tarski(A_126,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_20,c_421])).

tff(c_455,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_441])).

tff(c_58,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_458,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_58])).

tff(c_26,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_492,plain,(
    ! [A_130,B_131] :
      ( m1_subset_1(k1_orders_2(A_130,B_131),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_orders_2(A_130)
      | ~ v5_orders_2(A_130)
      | ~ v4_orders_2(A_130)
      | ~ v3_orders_2(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_503,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_492])).

tff(c_514,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_89,c_89,c_503])).

tff(c_515,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_514])).

tff(c_711,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_515])).

tff(c_737,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_711])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_737])).

tff(c_742,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_22,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1066,plain,(
    ! [A_171] :
      ( m1_subset_1(A_171,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_171,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_742,c_22])).

tff(c_1082,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1066])).

tff(c_1088,plain,(
    m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_1082])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_436,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) = a_2_0_orders_2('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_421])).

tff(c_506,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_492])).

tff(c_517,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_16,c_89,c_506])).

tff(c_518,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_517])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_532,plain,(
    r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_518,c_18])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_947,plain,(
    ! [D_162,B_163,C_164] :
      ( r2_hidden('#skF_4'(D_162,B_163,C_164,D_162),C_164)
      | r2_hidden(D_162,a_2_0_orders_2(B_163,C_164))
      | ~ m1_subset_1(D_162,u1_struct_0(B_163))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(u1_struct_0(B_163)))
      | ~ l1_orders_2(B_163)
      | ~ v5_orders_2(B_163)
      | ~ v4_orders_2(B_163)
      | ~ v3_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_960,plain,(
    ! [D_162,C_164] :
      ( r2_hidden('#skF_4'(D_162,'#skF_5',C_164,D_162),C_164)
      | r2_hidden(D_162,a_2_0_orders_2('#skF_5',C_164))
      | ~ m1_subset_1(D_162,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_947])).

tff(c_969,plain,(
    ! [D_162,C_164] :
      ( r2_hidden('#skF_4'(D_162,'#skF_5',C_164,D_162),C_164)
      | r2_hidden(D_162,a_2_0_orders_2('#skF_5',C_164))
      | ~ m1_subset_1(D_162,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_89,c_960])).

tff(c_995,plain,(
    ! [D_165,C_166] :
      ( r2_hidden('#skF_4'(D_165,'#skF_5',C_166,D_165),C_166)
      | r2_hidden(D_165,a_2_0_orders_2('#skF_5',C_166))
      | ~ m1_subset_1(D_165,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_969])).

tff(c_25041,plain,(
    ! [D_932] :
      ( r2_hidden('#skF_4'(D_932,'#skF_5',k1_xboole_0,D_932),k1_xboole_0)
      | r2_hidden(D_932,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_932,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16,c_995])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25063,plain,(
    ! [D_932] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4'(D_932,'#skF_5',k1_xboole_0,D_932))
      | r2_hidden(D_932,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_932,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_25041,c_24])).

tff(c_25146,plain,(
    ! [D_935] :
      ( r2_hidden(D_935,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_935,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_25063])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26223,plain,(
    ! [D_955,B_956] :
      ( r2_hidden(D_955,B_956)
      | ~ r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),B_956)
      | ~ m1_subset_1(D_955,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_25146,c_2])).

tff(c_26233,plain,(
    ! [D_955] :
      ( r2_hidden(D_955,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(D_955,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_532,c_26223])).

tff(c_154,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_17,B_78] :
      ( r2_hidden('#skF_2'(A_17),B_78)
      | ~ r1_tarski(A_17,B_78)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_26,c_154])).

tff(c_743,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_616,plain,(
    ! [A_134,B_135,C_136] :
      ( '#skF_3'(A_134,B_135,C_136) = A_134
      | ~ r2_hidden(A_134,a_2_0_orders_2(B_135,C_136))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(B_135)))
      | ~ l1_orders_2(B_135)
      | ~ v5_orders_2(B_135)
      | ~ v4_orders_2(B_135)
      | ~ v3_orders_2(B_135)
      | v2_struct_0(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6580,plain,(
    ! [B_456,C_457] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2(B_456,C_457)),B_456,C_457) = '#skF_2'(a_2_0_orders_2(B_456,C_457))
      | ~ m1_subset_1(C_457,k1_zfmisc_1(u1_struct_0(B_456)))
      | ~ l1_orders_2(B_456)
      | ~ v5_orders_2(B_456)
      | ~ v4_orders_2(B_456)
      | ~ v3_orders_2(B_456)
      | v2_struct_0(B_456)
      | a_2_0_orders_2(B_456,C_457) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_616])).

tff(c_6596,plain,(
    ! [C_457] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_457)),'#skF_5',C_457) = '#skF_2'(a_2_0_orders_2('#skF_5',C_457))
      | ~ m1_subset_1(C_457,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_457) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_6580])).

tff(c_6606,plain,(
    ! [C_457] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_457)),'#skF_5',C_457) = '#skF_2'(a_2_0_orders_2('#skF_5',C_457))
      | ~ m1_subset_1(C_457,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_457) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_6596])).

tff(c_6949,plain,(
    ! [C_478] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_478)),'#skF_5',C_478) = '#skF_2'(a_2_0_orders_2('#skF_5',C_478))
      | ~ m1_subset_1(C_478,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | a_2_0_orders_2('#skF_5',C_478) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6606])).

tff(c_6965,plain,
    ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_743,c_6949])).

tff(c_6993,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_6965])).

tff(c_4780,plain,(
    ! [B_351,E_352,A_353,C_354] :
      ( r2_orders_2(B_351,E_352,'#skF_3'(A_353,B_351,C_354))
      | ~ r2_hidden(E_352,C_354)
      | ~ m1_subset_1(E_352,u1_struct_0(B_351))
      | ~ r2_hidden(A_353,a_2_0_orders_2(B_351,C_354))
      | ~ m1_subset_1(C_354,k1_zfmisc_1(u1_struct_0(B_351)))
      | ~ l1_orders_2(B_351)
      | ~ v5_orders_2(B_351)
      | ~ v4_orders_2(B_351)
      | ~ v3_orders_2(B_351)
      | v2_struct_0(B_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_7152,plain,(
    ! [B_483,E_484,A_485,A_486] :
      ( r2_orders_2(B_483,E_484,'#skF_3'(A_485,B_483,A_486))
      | ~ r2_hidden(E_484,A_486)
      | ~ m1_subset_1(E_484,u1_struct_0(B_483))
      | ~ r2_hidden(A_485,a_2_0_orders_2(B_483,A_486))
      | ~ l1_orders_2(B_483)
      | ~ v5_orders_2(B_483)
      | ~ v4_orders_2(B_483)
      | ~ v3_orders_2(B_483)
      | v2_struct_0(B_483)
      | ~ r1_tarski(A_486,u1_struct_0(B_483)) ) ),
    inference(resolution,[status(thm)],[c_20,c_4780])).

tff(c_7163,plain,(
    ! [E_484] :
      ( r2_orders_2('#skF_5',E_484,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_484,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_484,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6993,c_7152])).

tff(c_7171,plain,(
    ! [E_484] :
      ( r2_orders_2('#skF_5',E_484,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_484,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_484,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89,c_66,c_64,c_62,c_60,c_89,c_7163])).

tff(c_7172,plain,(
    ! [E_484] :
      ( r2_orders_2('#skF_5',E_484,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_484,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_484,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7171])).

tff(c_11284,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_7172])).

tff(c_11287,plain,
    ( ~ r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_11284])).

tff(c_11293,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_11287])).

tff(c_11295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_11293])).

tff(c_11297,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_7172])).

tff(c_36,plain,(
    ! [A_28,C_34] :
      ( ~ r2_orders_2(A_28,C_34,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26284,plain,(
    ! [A_959,B_960,A_961] :
      ( ~ r2_hidden('#skF_3'(A_959,B_960,A_961),A_961)
      | ~ m1_subset_1('#skF_3'(A_959,B_960,A_961),u1_struct_0(B_960))
      | ~ r2_hidden(A_959,a_2_0_orders_2(B_960,A_961))
      | ~ l1_orders_2(B_960)
      | ~ v5_orders_2(B_960)
      | ~ v4_orders_2(B_960)
      | ~ v3_orders_2(B_960)
      | v2_struct_0(B_960)
      | ~ r1_tarski(A_961,u1_struct_0(B_960)) ) ),
    inference(resolution,[status(thm)],[c_7152,c_36])).

tff(c_26310,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6993,c_26284])).

tff(c_26330,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89,c_66,c_64,c_62,c_60,c_11297,c_1088,c_89,c_6993,c_26310])).

tff(c_26331,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_26330])).

tff(c_26337,plain,(
    ~ m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_26233,c_26331])).

tff(c_26359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_26337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:56:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.35/5.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.50/5.90  
% 13.50/5.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.50/5.90  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 13.50/5.90  
% 13.50/5.90  %Foreground sorts:
% 13.50/5.90  
% 13.50/5.90  
% 13.50/5.90  %Background operators:
% 13.50/5.90  
% 13.50/5.90  
% 13.50/5.90  %Foreground operators:
% 13.50/5.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.50/5.90  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 13.50/5.90  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 13.50/5.90  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.50/5.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.50/5.90  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 13.50/5.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.50/5.90  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.50/5.90  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 13.50/5.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.50/5.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.50/5.90  tff('#skF_5', type, '#skF_5': $i).
% 13.50/5.90  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 13.50/5.90  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 13.50/5.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.50/5.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.50/5.90  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 13.50/5.90  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 13.50/5.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.50/5.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.50/5.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.50/5.90  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 13.50/5.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.50/5.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.50/5.90  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 13.50/5.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.50/5.90  
% 13.50/5.92  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.50/5.92  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.50/5.92  tff(f_168, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 13.50/5.92  tff(f_127, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 13.50/5.92  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 13.50/5.92  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 13.50/5.92  tff(f_73, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 13.50/5.92  tff(f_123, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 13.50/5.92  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 13.50/5.92  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 13.50/5.92  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.50/5.92  tff(f_154, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 13.50/5.92  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 13.50/5.92  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.50/5.92  tff(f_92, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 13.50/5.92  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.50/5.92  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.50/5.92  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 13.50/5.92  tff(c_66, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 13.50/5.92  tff(c_64, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 13.50/5.92  tff(c_62, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 13.50/5.92  tff(c_60, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 13.50/5.92  tff(c_44, plain, (![A_40]: (l1_struct_0(A_40) | ~l1_orders_2(A_40))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.50/5.92  tff(c_75, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.50/5.92  tff(c_85, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_orders_2(A_62))), inference(resolution, [status(thm)], [c_44, c_75])).
% 13.50/5.92  tff(c_89, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_85])).
% 13.50/5.92  tff(c_356, plain, (![A_118, B_119]: (k1_orders_2(A_118, B_119)=a_2_0_orders_2(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.50/5.92  tff(c_367, plain, (![B_119]: (k1_orders_2('#skF_5', B_119)=a_2_0_orders_2('#skF_5', B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_356])).
% 13.50/5.92  tff(c_375, plain, (![B_119]: (k1_orders_2('#skF_5', B_119)=a_2_0_orders_2('#skF_5', B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_367])).
% 13.50/5.92  tff(c_421, plain, (![B_125]: (k1_orders_2('#skF_5', B_125)=a_2_0_orders_2('#skF_5', B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_375])).
% 13.50/5.92  tff(c_441, plain, (![A_126]: (k1_orders_2('#skF_5', A_126)=a_2_0_orders_2('#skF_5', A_126) | ~r1_tarski(A_126, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_20, c_421])).
% 13.50/5.92  tff(c_455, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_441])).
% 13.50/5.92  tff(c_58, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_168])).
% 13.50/5.92  tff(c_458, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_455, c_58])).
% 13.50/5.92  tff(c_26, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.50/5.92  tff(c_492, plain, (![A_130, B_131]: (m1_subset_1(k1_orders_2(A_130, B_131), k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_orders_2(A_130) | ~v5_orders_2(A_130) | ~v4_orders_2(A_130) | ~v3_orders_2(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_123])).
% 13.50/5.92  tff(c_503, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_455, c_492])).
% 13.50/5.92  tff(c_514, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_89, c_89, c_503])).
% 13.50/5.92  tff(c_515, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_514])).
% 13.50/5.92  tff(c_711, plain, (~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_515])).
% 13.50/5.92  tff(c_737, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_711])).
% 13.50/5.92  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_737])).
% 13.50/5.92  tff(c_742, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_515])).
% 13.50/5.92  tff(c_22, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.50/5.92  tff(c_1066, plain, (![A_171]: (m1_subset_1(A_171, k2_struct_0('#skF_5')) | ~r2_hidden(A_171, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_742, c_22])).
% 13.50/5.92  tff(c_1082, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_1066])).
% 13.50/5.92  tff(c_1088, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_458, c_1082])).
% 13.50/5.92  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.50/5.92  tff(c_436, plain, (k1_orders_2('#skF_5', k1_xboole_0)=a_2_0_orders_2('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_421])).
% 13.50/5.92  tff(c_506, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_436, c_492])).
% 13.50/5.92  tff(c_517, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_16, c_89, c_506])).
% 13.50/5.92  tff(c_518, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_517])).
% 13.50/5.92  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.50/5.92  tff(c_532, plain, (r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_518, c_18])).
% 13.50/5.92  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.50/5.92  tff(c_947, plain, (![D_162, B_163, C_164]: (r2_hidden('#skF_4'(D_162, B_163, C_164, D_162), C_164) | r2_hidden(D_162, a_2_0_orders_2(B_163, C_164)) | ~m1_subset_1(D_162, u1_struct_0(B_163)) | ~m1_subset_1(C_164, k1_zfmisc_1(u1_struct_0(B_163))) | ~l1_orders_2(B_163) | ~v5_orders_2(B_163) | ~v4_orders_2(B_163) | ~v3_orders_2(B_163) | v2_struct_0(B_163))), inference(cnfTransformation, [status(thm)], [f_154])).
% 13.50/5.92  tff(c_960, plain, (![D_162, C_164]: (r2_hidden('#skF_4'(D_162, '#skF_5', C_164, D_162), C_164) | r2_hidden(D_162, a_2_0_orders_2('#skF_5', C_164)) | ~m1_subset_1(D_162, u1_struct_0('#skF_5')) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_947])).
% 13.50/5.92  tff(c_969, plain, (![D_162, C_164]: (r2_hidden('#skF_4'(D_162, '#skF_5', C_164, D_162), C_164) | r2_hidden(D_162, a_2_0_orders_2('#skF_5', C_164)) | ~m1_subset_1(D_162, k2_struct_0('#skF_5')) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_89, c_960])).
% 13.50/5.92  tff(c_995, plain, (![D_165, C_166]: (r2_hidden('#skF_4'(D_165, '#skF_5', C_166, D_165), C_166) | r2_hidden(D_165, a_2_0_orders_2('#skF_5', C_166)) | ~m1_subset_1(D_165, k2_struct_0('#skF_5')) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_969])).
% 13.50/5.92  tff(c_25041, plain, (![D_932]: (r2_hidden('#skF_4'(D_932, '#skF_5', k1_xboole_0, D_932), k1_xboole_0) | r2_hidden(D_932, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_932, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16, c_995])).
% 13.50/5.92  tff(c_24, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.50/5.92  tff(c_25063, plain, (![D_932]: (~r1_tarski(k1_xboole_0, '#skF_4'(D_932, '#skF_5', k1_xboole_0, D_932)) | r2_hidden(D_932, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_932, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_25041, c_24])).
% 13.50/5.92  tff(c_25146, plain, (![D_935]: (r2_hidden(D_935, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_935, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_25063])).
% 13.50/5.92  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.50/5.92  tff(c_26223, plain, (![D_955, B_956]: (r2_hidden(D_955, B_956) | ~r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), B_956) | ~m1_subset_1(D_955, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_25146, c_2])).
% 13.50/5.92  tff(c_26233, plain, (![D_955]: (r2_hidden(D_955, k2_struct_0('#skF_5')) | ~m1_subset_1(D_955, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_532, c_26223])).
% 13.50/5.92  tff(c_154, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.50/5.92  tff(c_160, plain, (![A_17, B_78]: (r2_hidden('#skF_2'(A_17), B_78) | ~r1_tarski(A_17, B_78) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_26, c_154])).
% 13.50/5.92  tff(c_743, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_515])).
% 13.50/5.92  tff(c_616, plain, (![A_134, B_135, C_136]: ('#skF_3'(A_134, B_135, C_136)=A_134 | ~r2_hidden(A_134, a_2_0_orders_2(B_135, C_136)) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(B_135))) | ~l1_orders_2(B_135) | ~v5_orders_2(B_135) | ~v4_orders_2(B_135) | ~v3_orders_2(B_135) | v2_struct_0(B_135))), inference(cnfTransformation, [status(thm)], [f_154])).
% 13.50/5.92  tff(c_6580, plain, (![B_456, C_457]: ('#skF_3'('#skF_2'(a_2_0_orders_2(B_456, C_457)), B_456, C_457)='#skF_2'(a_2_0_orders_2(B_456, C_457)) | ~m1_subset_1(C_457, k1_zfmisc_1(u1_struct_0(B_456))) | ~l1_orders_2(B_456) | ~v5_orders_2(B_456) | ~v4_orders_2(B_456) | ~v3_orders_2(B_456) | v2_struct_0(B_456) | a_2_0_orders_2(B_456, C_457)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_616])).
% 13.50/5.92  tff(c_6596, plain, (![C_457]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_457)), '#skF_5', C_457)='#skF_2'(a_2_0_orders_2('#skF_5', C_457)) | ~m1_subset_1(C_457, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_457)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_89, c_6580])).
% 13.50/5.92  tff(c_6606, plain, (![C_457]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_457)), '#skF_5', C_457)='#skF_2'(a_2_0_orders_2('#skF_5', C_457)) | ~m1_subset_1(C_457, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_457)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_6596])).
% 13.50/5.92  tff(c_6949, plain, (![C_478]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_478)), '#skF_5', C_478)='#skF_2'(a_2_0_orders_2('#skF_5', C_478)) | ~m1_subset_1(C_478, k1_zfmisc_1(k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', C_478)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_68, c_6606])).
% 13.50/5.92  tff(c_6965, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_743, c_6949])).
% 13.50/5.92  tff(c_6993, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_458, c_6965])).
% 13.50/5.92  tff(c_4780, plain, (![B_351, E_352, A_353, C_354]: (r2_orders_2(B_351, E_352, '#skF_3'(A_353, B_351, C_354)) | ~r2_hidden(E_352, C_354) | ~m1_subset_1(E_352, u1_struct_0(B_351)) | ~r2_hidden(A_353, a_2_0_orders_2(B_351, C_354)) | ~m1_subset_1(C_354, k1_zfmisc_1(u1_struct_0(B_351))) | ~l1_orders_2(B_351) | ~v5_orders_2(B_351) | ~v4_orders_2(B_351) | ~v3_orders_2(B_351) | v2_struct_0(B_351))), inference(cnfTransformation, [status(thm)], [f_154])).
% 13.50/5.92  tff(c_7152, plain, (![B_483, E_484, A_485, A_486]: (r2_orders_2(B_483, E_484, '#skF_3'(A_485, B_483, A_486)) | ~r2_hidden(E_484, A_486) | ~m1_subset_1(E_484, u1_struct_0(B_483)) | ~r2_hidden(A_485, a_2_0_orders_2(B_483, A_486)) | ~l1_orders_2(B_483) | ~v5_orders_2(B_483) | ~v4_orders_2(B_483) | ~v3_orders_2(B_483) | v2_struct_0(B_483) | ~r1_tarski(A_486, u1_struct_0(B_483)))), inference(resolution, [status(thm)], [c_20, c_4780])).
% 13.50/5.92  tff(c_7163, plain, (![E_484]: (r2_orders_2('#skF_5', E_484, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_484, k2_struct_0('#skF_5')) | ~m1_subset_1(E_484, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6993, c_7152])).
% 13.50/5.92  tff(c_7171, plain, (![E_484]: (r2_orders_2('#skF_5', E_484, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_484, k2_struct_0('#skF_5')) | ~m1_subset_1(E_484, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89, c_66, c_64, c_62, c_60, c_89, c_7163])).
% 13.50/5.92  tff(c_7172, plain, (![E_484]: (r2_orders_2('#skF_5', E_484, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_484, k2_struct_0('#skF_5')) | ~m1_subset_1(E_484, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_7171])).
% 13.50/5.92  tff(c_11284, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_7172])).
% 13.50/5.92  tff(c_11287, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_160, c_11284])).
% 13.50/5.92  tff(c_11293, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_11287])).
% 13.50/5.92  tff(c_11295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_458, c_11293])).
% 13.50/5.92  tff(c_11297, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_7172])).
% 13.50/5.92  tff(c_36, plain, (![A_28, C_34]: (~r2_orders_2(A_28, C_34, C_34) | ~m1_subset_1(C_34, u1_struct_0(A_28)) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.50/5.92  tff(c_26284, plain, (![A_959, B_960, A_961]: (~r2_hidden('#skF_3'(A_959, B_960, A_961), A_961) | ~m1_subset_1('#skF_3'(A_959, B_960, A_961), u1_struct_0(B_960)) | ~r2_hidden(A_959, a_2_0_orders_2(B_960, A_961)) | ~l1_orders_2(B_960) | ~v5_orders_2(B_960) | ~v4_orders_2(B_960) | ~v3_orders_2(B_960) | v2_struct_0(B_960) | ~r1_tarski(A_961, u1_struct_0(B_960)))), inference(resolution, [status(thm)], [c_7152, c_36])).
% 13.50/5.92  tff(c_26310, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6993, c_26284])).
% 13.50/5.92  tff(c_26330, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89, c_66, c_64, c_62, c_60, c_11297, c_1088, c_89, c_6993, c_26310])).
% 13.50/5.92  tff(c_26331, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_26330])).
% 13.50/5.92  tff(c_26337, plain, (~m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_26233, c_26331])).
% 13.50/5.92  tff(c_26359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1088, c_26337])).
% 13.50/5.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.50/5.92  
% 13.50/5.92  Inference rules
% 13.50/5.92  ----------------------
% 13.50/5.92  #Ref     : 0
% 13.50/5.92  #Sup     : 6281
% 13.50/5.92  #Fact    : 0
% 13.50/5.92  #Define  : 0
% 13.50/5.92  #Split   : 30
% 13.50/5.92  #Chain   : 0
% 13.50/5.92  #Close   : 0
% 13.50/5.92  
% 13.50/5.92  Ordering : KBO
% 13.50/5.92  
% 13.50/5.92  Simplification rules
% 13.50/5.92  ----------------------
% 13.50/5.92  #Subsume      : 2485
% 13.50/5.92  #Demod        : 3241
% 13.50/5.92  #Tautology    : 842
% 13.50/5.92  #SimpNegUnit  : 362
% 13.50/5.92  #BackRed      : 55
% 13.50/5.92  
% 13.50/5.92  #Partial instantiations: 0
% 13.50/5.92  #Strategies tried      : 1
% 13.50/5.92  
% 13.50/5.92  Timing (in seconds)
% 13.50/5.92  ----------------------
% 13.50/5.93  Preprocessing        : 0.38
% 13.50/5.93  Parsing              : 0.16
% 13.50/5.93  CNF conversion       : 0.04
% 13.50/5.93  Main loop            : 4.67
% 13.50/5.93  Inferencing          : 1.00
% 13.50/5.93  Reduction            : 1.31
% 13.50/5.93  Demodulation         : 0.88
% 13.50/5.93  BG Simplification    : 0.11
% 13.50/5.93  Subsumption          : 1.94
% 13.50/5.93  Abstraction          : 0.16
% 13.50/5.93  MUC search           : 0.00
% 13.50/5.93  Cooper               : 0.00
% 13.50/5.93  Total                : 5.09
% 13.50/5.93  Index Insertion      : 0.00
% 13.50/5.93  Index Deletion       : 0.00
% 13.50/5.93  Index Matching       : 0.00
% 13.50/5.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
