%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:23 EST 2020

% Result     : Theorem 16.68s
% Output     : CNFRefutation 16.68s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 356 expanded)
%              Number of leaves         :   36 ( 148 expanded)
%              Depth                    :   25
%              Number of atoms          :  268 (1209 expanded)
%              Number of equality atoms :   20 ( 120 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_77,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_123,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_148,plain,(
    ! [A_66,B_67] :
      ( k1_orders_2(A_66,B_67) = a_2_0_orders_2(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_570,plain,(
    ! [A_123] :
      ( k1_orders_2(A_123,k1_xboole_0) = a_2_0_orders_2(A_123,k1_xboole_0)
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_16,c_148])).

tff(c_573,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0)
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_570])).

tff(c_576,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_573])).

tff(c_577,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_576])).

tff(c_32,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,(
    ! [A_41] :
      ( k1_struct_0(A_41) = k1_xboole_0
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [A_42] :
      ( k1_struct_0(A_42) = k1_xboole_0
      | ~ l1_orders_2(A_42) ) ),
    inference(resolution,[status(thm)],[c_32,c_62])).

tff(c_71,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_46,plain,(
    k1_orders_2('#skF_4',k1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_72,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_46])).

tff(c_578,plain,(
    a_2_0_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_72])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k1_orders_2(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_orders_2(A_21)
      | ~ v5_orders_2(A_21)
      | ~ v4_orders_2(A_21)
      | ~ v3_orders_2(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_582,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_30])).

tff(c_586,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_16,c_582])).

tff(c_587,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_586])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_614,plain,(
    r1_tarski(a_2_0_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_587,c_18])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_631,plain,
    ( a_2_0_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_614,c_8])).

tff(c_638,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_578,c_631])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_680,plain,(
    ! [A_125,A_126] :
      ( k1_orders_2(A_125,A_126) = a_2_0_orders_2(A_125,A_126)
      | ~ l1_orders_2(A_125)
      | ~ v5_orders_2(A_125)
      | ~ v4_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v2_struct_0(A_125)
      | ~ r1_tarski(A_126,u1_struct_0(A_125)) ) ),
    inference(resolution,[status(thm)],[c_20,c_148])).

tff(c_706,plain,(
    ! [A_125] :
      ( k1_orders_2(A_125,u1_struct_0(A_125)) = a_2_0_orders_2(A_125,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | ~ v5_orders_2(A_125)
      | ~ v4_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_12,c_680])).

tff(c_198,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k1_orders_2(A_77,B_78),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_944,plain,(
    ! [A_145,A_146,B_147] :
      ( m1_subset_1(A_145,u1_struct_0(A_146))
      | ~ r2_hidden(A_145,k1_orders_2(A_146,B_147))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146)
      | ~ v4_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_198,c_22])).

tff(c_967,plain,(
    ! [A_146,B_147,B_2] :
      ( m1_subset_1('#skF_1'(k1_orders_2(A_146,B_147),B_2),u1_struct_0(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146)
      | ~ v4_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146)
      | r1_tarski(k1_orders_2(A_146,B_147),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_944])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_367,plain,(
    ! [D_96,B_97,C_98] :
      ( r2_hidden('#skF_3'(D_96,B_97,C_98,D_96),C_98)
      | r2_hidden(D_96,a_2_0_orders_2(B_97,C_98))
      | ~ m1_subset_1(D_96,u1_struct_0(B_97))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(B_97)))
      | ~ l1_orders_2(B_97)
      | ~ v5_orders_2(B_97)
      | ~ v4_orders_2(B_97)
      | ~ v3_orders_2(B_97)
      | v2_struct_0(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1350,plain,(
    ! [D_164,B_165] :
      ( r2_hidden('#skF_3'(D_164,B_165,k1_xboole_0,D_164),k1_xboole_0)
      | r2_hidden(D_164,a_2_0_orders_2(B_165,k1_xboole_0))
      | ~ m1_subset_1(D_164,u1_struct_0(B_165))
      | ~ l1_orders_2(B_165)
      | ~ v5_orders_2(B_165)
      | ~ v4_orders_2(B_165)
      | ~ v3_orders_2(B_165)
      | v2_struct_0(B_165) ) ),
    inference(resolution,[status(thm)],[c_16,c_367])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1365,plain,(
    ! [D_164,B_165] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'(D_164,B_165,k1_xboole_0,D_164))
      | r2_hidden(D_164,a_2_0_orders_2(B_165,k1_xboole_0))
      | ~ m1_subset_1(D_164,u1_struct_0(B_165))
      | ~ l1_orders_2(B_165)
      | ~ v5_orders_2(B_165)
      | ~ v4_orders_2(B_165)
      | ~ v3_orders_2(B_165)
      | v2_struct_0(B_165) ) ),
    inference(resolution,[status(thm)],[c_1350,c_24])).

tff(c_5230,plain,(
    ! [D_294,B_295] :
      ( r2_hidden(D_294,a_2_0_orders_2(B_295,k1_xboole_0))
      | ~ m1_subset_1(D_294,u1_struct_0(B_295))
      | ~ l1_orders_2(B_295)
      | ~ v5_orders_2(B_295)
      | ~ v4_orders_2(B_295)
      | ~ v3_orders_2(B_295)
      | v2_struct_0(B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1365])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36966,plain,(
    ! [D_712,B_713,B_714] :
      ( r2_hidden(D_712,B_713)
      | ~ r1_tarski(a_2_0_orders_2(B_714,k1_xboole_0),B_713)
      | ~ m1_subset_1(D_712,u1_struct_0(B_714))
      | ~ l1_orders_2(B_714)
      | ~ v5_orders_2(B_714)
      | ~ v4_orders_2(B_714)
      | ~ v3_orders_2(B_714)
      | v2_struct_0(B_714) ) ),
    inference(resolution,[status(thm)],[c_5230,c_2])).

tff(c_36968,plain,(
    ! [D_712] :
      ( r2_hidden(D_712,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_712,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_614,c_36966])).

tff(c_36977,plain,(
    ! [D_712] :
      ( r2_hidden(D_712,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_712,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_36968])).

tff(c_36981,plain,(
    ! [D_715] :
      ( r2_hidden(D_715,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_715,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_36977])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37115,plain,(
    ! [A_722] :
      ( r1_tarski(A_722,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_722,u1_struct_0('#skF_4')),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36981,c_4])).

tff(c_37227,plain,(
    ! [B_147] :
      ( ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tarski(k1_orders_2('#skF_4',B_147),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_967,c_37115])).

tff(c_37274,plain,(
    ! [B_147] :
      ( ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | r1_tarski(k1_orders_2('#skF_4',B_147),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_37227])).

tff(c_37282,plain,(
    ! [B_723] :
      ( ~ m1_subset_1(B_723,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tarski(k1_orders_2('#skF_4',B_723),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_37274])).

tff(c_37315,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r1_tarski(a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_37282])).

tff(c_37350,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r1_tarski(a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_37315])).

tff(c_37351,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r1_tarski(a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_37350])).

tff(c_37362,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_37351])).

tff(c_37374,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_37362])).

tff(c_37381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_37374])).

tff(c_37383,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_37351])).

tff(c_37684,plain,(
    ! [A_727] :
      ( m1_subset_1(A_727,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_727,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_37383,c_22])).

tff(c_37735,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_2),u1_struct_0('#skF_4'))
      | r1_tarski(u1_struct_0('#skF_4'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_37684])).

tff(c_38143,plain,(
    ! [A_732,B_733] :
      ( r1_tarski(A_732,a_2_0_orders_2(B_733,k1_xboole_0))
      | ~ m1_subset_1('#skF_1'(A_732,a_2_0_orders_2(B_733,k1_xboole_0)),u1_struct_0(B_733))
      | ~ l1_orders_2(B_733)
      | ~ v5_orders_2(B_733)
      | ~ v4_orders_2(B_733)
      | ~ v3_orders_2(B_733)
      | v2_struct_0(B_733) ) ),
    inference(resolution,[status(thm)],[c_5230,c_4])).

tff(c_38147,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_37735,c_38143])).

tff(c_38308,plain,
    ( v2_struct_0('#skF_4')
    | r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_38147])).

tff(c_38310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_56,c_38308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.68/8.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.68/8.67  
% 16.68/8.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.68/8.67  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 16.68/8.67  
% 16.68/8.67  %Foreground sorts:
% 16.68/8.67  
% 16.68/8.67  
% 16.68/8.67  %Background operators:
% 16.68/8.67  
% 16.68/8.67  
% 16.68/8.67  %Foreground operators:
% 16.68/8.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.68/8.67  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 16.68/8.67  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 16.68/8.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.68/8.67  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 16.68/8.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.68/8.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.68/8.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.68/8.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.68/8.67  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 16.68/8.67  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 16.68/8.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.68/8.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 16.68/8.67  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 16.68/8.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.68/8.67  tff('#skF_4', type, '#skF_4': $i).
% 16.68/8.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.68/8.67  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 16.68/8.67  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 16.68/8.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 16.68/8.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.68/8.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.68/8.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.68/8.67  
% 16.68/8.69  tff(f_137, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_orders_2)).
% 16.68/8.69  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 16.68/8.69  tff(f_77, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 16.68/8.69  tff(f_96, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 16.68/8.69  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 16.68/8.69  tff(f_92, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 16.68/8.69  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.68/8.69  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.68/8.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.68/8.69  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 16.68/8.69  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.68/8.69  tff(f_123, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 16.68/8.69  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 16.68/8.69  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.68/8.69  tff(c_54, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.68/8.69  tff(c_52, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.68/8.69  tff(c_48, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.68/8.69  tff(c_50, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.68/8.69  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.68/8.69  tff(c_148, plain, (![A_66, B_67]: (k1_orders_2(A_66, B_67)=a_2_0_orders_2(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_orders_2(A_66) | ~v5_orders_2(A_66) | ~v4_orders_2(A_66) | ~v3_orders_2(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.68/8.69  tff(c_570, plain, (![A_123]: (k1_orders_2(A_123, k1_xboole_0)=a_2_0_orders_2(A_123, k1_xboole_0) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_16, c_148])).
% 16.68/8.69  tff(c_573, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_570])).
% 16.68/8.69  tff(c_576, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_573])).
% 16.68/8.69  tff(c_577, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_576])).
% 16.68/8.69  tff(c_32, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 16.68/8.69  tff(c_62, plain, (![A_41]: (k1_struct_0(A_41)=k1_xboole_0 | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.68/8.69  tff(c_67, plain, (![A_42]: (k1_struct_0(A_42)=k1_xboole_0 | ~l1_orders_2(A_42))), inference(resolution, [status(thm)], [c_32, c_62])).
% 16.68/8.69  tff(c_71, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_67])).
% 16.68/8.69  tff(c_46, plain, (k1_orders_2('#skF_4', k1_struct_0('#skF_4'))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.68/8.69  tff(c_72, plain, (k1_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_46])).
% 16.68/8.69  tff(c_578, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_72])).
% 16.68/8.69  tff(c_30, plain, (![A_21, B_22]: (m1_subset_1(k1_orders_2(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_orders_2(A_21) | ~v5_orders_2(A_21) | ~v4_orders_2(A_21) | ~v3_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.68/8.69  tff(c_582, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_577, c_30])).
% 16.68/8.69  tff(c_586, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_16, c_582])).
% 16.68/8.69  tff(c_587, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_586])).
% 16.68/8.69  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.68/8.69  tff(c_614, plain, (r1_tarski(a_2_0_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_587, c_18])).
% 16.68/8.69  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.68/8.69  tff(c_631, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_614, c_8])).
% 16.68/8.69  tff(c_638, plain, (~r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_578, c_631])).
% 16.68/8.69  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.68/8.69  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.68/8.69  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.68/8.69  tff(c_680, plain, (![A_125, A_126]: (k1_orders_2(A_125, A_126)=a_2_0_orders_2(A_125, A_126) | ~l1_orders_2(A_125) | ~v5_orders_2(A_125) | ~v4_orders_2(A_125) | ~v3_orders_2(A_125) | v2_struct_0(A_125) | ~r1_tarski(A_126, u1_struct_0(A_125)))), inference(resolution, [status(thm)], [c_20, c_148])).
% 16.68/8.69  tff(c_706, plain, (![A_125]: (k1_orders_2(A_125, u1_struct_0(A_125))=a_2_0_orders_2(A_125, u1_struct_0(A_125)) | ~l1_orders_2(A_125) | ~v5_orders_2(A_125) | ~v4_orders_2(A_125) | ~v3_orders_2(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_12, c_680])).
% 16.68/8.69  tff(c_198, plain, (![A_77, B_78]: (m1_subset_1(k1_orders_2(A_77, B_78), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.68/8.69  tff(c_22, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.68/8.69  tff(c_944, plain, (![A_145, A_146, B_147]: (m1_subset_1(A_145, u1_struct_0(A_146)) | ~r2_hidden(A_145, k1_orders_2(A_146, B_147)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_orders_2(A_146) | ~v5_orders_2(A_146) | ~v4_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146))), inference(resolution, [status(thm)], [c_198, c_22])).
% 16.68/8.69  tff(c_967, plain, (![A_146, B_147, B_2]: (m1_subset_1('#skF_1'(k1_orders_2(A_146, B_147), B_2), u1_struct_0(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_orders_2(A_146) | ~v5_orders_2(A_146) | ~v4_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146) | r1_tarski(k1_orders_2(A_146, B_147), B_2))), inference(resolution, [status(thm)], [c_6, c_944])).
% 16.68/8.69  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 16.68/8.69  tff(c_367, plain, (![D_96, B_97, C_98]: (r2_hidden('#skF_3'(D_96, B_97, C_98, D_96), C_98) | r2_hidden(D_96, a_2_0_orders_2(B_97, C_98)) | ~m1_subset_1(D_96, u1_struct_0(B_97)) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(B_97))) | ~l1_orders_2(B_97) | ~v5_orders_2(B_97) | ~v4_orders_2(B_97) | ~v3_orders_2(B_97) | v2_struct_0(B_97))), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.68/8.69  tff(c_1350, plain, (![D_164, B_165]: (r2_hidden('#skF_3'(D_164, B_165, k1_xboole_0, D_164), k1_xboole_0) | r2_hidden(D_164, a_2_0_orders_2(B_165, k1_xboole_0)) | ~m1_subset_1(D_164, u1_struct_0(B_165)) | ~l1_orders_2(B_165) | ~v5_orders_2(B_165) | ~v4_orders_2(B_165) | ~v3_orders_2(B_165) | v2_struct_0(B_165))), inference(resolution, [status(thm)], [c_16, c_367])).
% 16.68/8.69  tff(c_24, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.68/8.69  tff(c_1365, plain, (![D_164, B_165]: (~r1_tarski(k1_xboole_0, '#skF_3'(D_164, B_165, k1_xboole_0, D_164)) | r2_hidden(D_164, a_2_0_orders_2(B_165, k1_xboole_0)) | ~m1_subset_1(D_164, u1_struct_0(B_165)) | ~l1_orders_2(B_165) | ~v5_orders_2(B_165) | ~v4_orders_2(B_165) | ~v3_orders_2(B_165) | v2_struct_0(B_165))), inference(resolution, [status(thm)], [c_1350, c_24])).
% 16.68/8.69  tff(c_5230, plain, (![D_294, B_295]: (r2_hidden(D_294, a_2_0_orders_2(B_295, k1_xboole_0)) | ~m1_subset_1(D_294, u1_struct_0(B_295)) | ~l1_orders_2(B_295) | ~v5_orders_2(B_295) | ~v4_orders_2(B_295) | ~v3_orders_2(B_295) | v2_struct_0(B_295))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1365])).
% 16.68/8.69  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.68/8.69  tff(c_36966, plain, (![D_712, B_713, B_714]: (r2_hidden(D_712, B_713) | ~r1_tarski(a_2_0_orders_2(B_714, k1_xboole_0), B_713) | ~m1_subset_1(D_712, u1_struct_0(B_714)) | ~l1_orders_2(B_714) | ~v5_orders_2(B_714) | ~v4_orders_2(B_714) | ~v3_orders_2(B_714) | v2_struct_0(B_714))), inference(resolution, [status(thm)], [c_5230, c_2])).
% 16.68/8.69  tff(c_36968, plain, (![D_712]: (r2_hidden(D_712, u1_struct_0('#skF_4')) | ~m1_subset_1(D_712, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_614, c_36966])).
% 16.68/8.69  tff(c_36977, plain, (![D_712]: (r2_hidden(D_712, u1_struct_0('#skF_4')) | ~m1_subset_1(D_712, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_36968])).
% 16.68/8.69  tff(c_36981, plain, (![D_715]: (r2_hidden(D_715, u1_struct_0('#skF_4')) | ~m1_subset_1(D_715, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_36977])).
% 16.68/8.69  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.68/8.69  tff(c_37115, plain, (![A_722]: (r1_tarski(A_722, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(A_722, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_36981, c_4])).
% 16.68/8.69  tff(c_37227, plain, (![B_147]: (~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(k1_orders_2('#skF_4', B_147), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_967, c_37115])).
% 16.68/8.69  tff(c_37274, plain, (![B_147]: (~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | r1_tarski(k1_orders_2('#skF_4', B_147), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_37227])).
% 16.68/8.69  tff(c_37282, plain, (![B_723]: (~m1_subset_1(B_723, k1_zfmisc_1(u1_struct_0('#skF_4'))) | r1_tarski(k1_orders_2('#skF_4', B_723), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_37274])).
% 16.68/8.69  tff(c_37315, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r1_tarski(a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_706, c_37282])).
% 16.68/8.69  tff(c_37350, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r1_tarski(a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_37315])).
% 16.68/8.69  tff(c_37351, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r1_tarski(a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_37350])).
% 16.68/8.69  tff(c_37362, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_37351])).
% 16.68/8.69  tff(c_37374, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_37362])).
% 16.68/8.69  tff(c_37381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_37374])).
% 16.68/8.69  tff(c_37383, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_37351])).
% 16.68/8.69  tff(c_37684, plain, (![A_727]: (m1_subset_1(A_727, u1_struct_0('#skF_4')) | ~r2_hidden(A_727, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_37383, c_22])).
% 16.68/8.69  tff(c_37735, plain, (![B_2]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_2), u1_struct_0('#skF_4')) | r1_tarski(u1_struct_0('#skF_4'), B_2))), inference(resolution, [status(thm)], [c_6, c_37684])).
% 16.68/8.69  tff(c_38143, plain, (![A_732, B_733]: (r1_tarski(A_732, a_2_0_orders_2(B_733, k1_xboole_0)) | ~m1_subset_1('#skF_1'(A_732, a_2_0_orders_2(B_733, k1_xboole_0)), u1_struct_0(B_733)) | ~l1_orders_2(B_733) | ~v5_orders_2(B_733) | ~v4_orders_2(B_733) | ~v3_orders_2(B_733) | v2_struct_0(B_733))), inference(resolution, [status(thm)], [c_5230, c_4])).
% 16.68/8.69  tff(c_38147, plain, (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_37735, c_38143])).
% 16.68/8.69  tff(c_38308, plain, (v2_struct_0('#skF_4') | r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_38147])).
% 16.68/8.69  tff(c_38310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_638, c_56, c_38308])).
% 16.68/8.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.68/8.69  
% 16.68/8.69  Inference rules
% 16.68/8.69  ----------------------
% 16.68/8.69  #Ref     : 0
% 16.68/8.69  #Sup     : 10056
% 16.68/8.69  #Fact    : 12
% 16.68/8.69  #Define  : 0
% 16.68/8.69  #Split   : 16
% 16.68/8.69  #Chain   : 0
% 16.68/8.69  #Close   : 0
% 16.68/8.69  
% 16.68/8.69  Ordering : KBO
% 16.68/8.69  
% 16.68/8.69  Simplification rules
% 16.68/8.69  ----------------------
% 16.68/8.69  #Subsume      : 4201
% 16.68/8.69  #Demod        : 4031
% 16.68/8.69  #Tautology    : 1941
% 16.68/8.69  #SimpNegUnit  : 460
% 16.68/8.69  #BackRed      : 10
% 16.68/8.69  
% 16.68/8.69  #Partial instantiations: 0
% 16.68/8.69  #Strategies tried      : 1
% 16.68/8.69  
% 16.68/8.69  Timing (in seconds)
% 16.68/8.69  ----------------------
% 16.68/8.70  Preprocessing        : 0.34
% 16.68/8.70  Parsing              : 0.18
% 16.68/8.70  CNF conversion       : 0.02
% 16.68/8.70  Main loop            : 7.57
% 16.68/8.70  Inferencing          : 1.16
% 16.68/8.70  Reduction            : 1.63
% 16.68/8.70  Demodulation         : 1.18
% 16.68/8.70  BG Simplification    : 0.14
% 16.68/8.70  Subsumption          : 4.29
% 16.68/8.70  Abstraction          : 0.23
% 16.68/8.70  MUC search           : 0.00
% 16.68/8.70  Cooper               : 0.00
% 16.68/8.70  Total                : 7.94
% 16.68/8.70  Index Insertion      : 0.00
% 16.68/8.70  Index Deletion       : 0.00
% 16.68/8.70  Index Matching       : 0.00
% 16.68/8.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
