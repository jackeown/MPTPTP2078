%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:27 EST 2020

% Result     : Theorem 11.09s
% Output     : CNFRefutation 11.09s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 390 expanded)
%              Number of leaves         :   40 ( 160 expanded)
%              Depth                    :   18
%              Number of atoms          :  247 (1213 expanded)
%              Number of equality atoms :   21 ( 135 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_74,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_72,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_70,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_68,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_26,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_271,plain,(
    ! [A_98,B_99] :
      ( k2_orders_2(A_98,B_99) = a_2_1_orders_2(A_98,B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1354,plain,(
    ! [A_212] :
      ( k2_orders_2(A_212,k1_xboole_0) = a_2_1_orders_2(A_212,k1_xboole_0)
      | ~ l1_orders_2(A_212)
      | ~ v5_orders_2(A_212)
      | ~ v4_orders_2(A_212)
      | ~ v3_orders_2(A_212)
      | v2_struct_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_26,c_271])).

tff(c_1357,plain,
    ( k2_orders_2('#skF_5',k1_xboole_0) = a_2_1_orders_2('#skF_5',k1_xboole_0)
    | ~ l1_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_1354])).

tff(c_1360,plain,
    ( k2_orders_2('#skF_5',k1_xboole_0) = a_2_1_orders_2('#skF_5',k1_xboole_0)
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1357])).

tff(c_1361,plain,(
    k2_orders_2('#skF_5',k1_xboole_0) = a_2_1_orders_2('#skF_5',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1360])).

tff(c_50,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_orders_2(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v3_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1366,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_50])).

tff(c_1370,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_26,c_1366])).

tff(c_1371,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1370])).

tff(c_42,plain,(
    ! [C_26,B_25,A_24] :
      ( ~ v1_xboole_0(C_26)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_26))
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1404,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_24,a_2_1_orders_2('#skF_5',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1371,c_42])).

tff(c_1416,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_148,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(B_10,A_9)
      | ~ r2_hidden(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_159,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1('#skF_1'(A_70,B_71),A_70)
      | v1_xboole_0(A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_148,c_18])).

tff(c_193,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ v1_xboole_0(C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_200,plain,(
    ! [A_11,A_82] :
      ( ~ v1_xboole_0(A_11)
      | ~ r2_hidden(A_82,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_193])).

tff(c_209,plain,(
    ! [A_82] : ~ r2_hidden(A_82,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_941,plain,(
    ! [D_166,B_167,C_168] :
      ( r2_hidden('#skF_4'(D_166,B_167,C_168,D_166),C_168)
      | r2_hidden(D_166,a_2_1_orders_2(B_167,C_168))
      | ~ m1_subset_1(D_166,u1_struct_0(B_167))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(B_167)))
      | ~ l1_orders_2(B_167)
      | ~ v5_orders_2(B_167)
      | ~ v4_orders_2(B_167)
      | ~ v3_orders_2(B_167)
      | v2_struct_0(B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_967,plain,(
    ! [D_166,B_167] :
      ( r2_hidden('#skF_4'(D_166,B_167,k1_xboole_0,D_166),k1_xboole_0)
      | r2_hidden(D_166,a_2_1_orders_2(B_167,k1_xboole_0))
      | ~ m1_subset_1(D_166,u1_struct_0(B_167))
      | ~ l1_orders_2(B_167)
      | ~ v5_orders_2(B_167)
      | ~ v4_orders_2(B_167)
      | ~ v3_orders_2(B_167)
      | v2_struct_0(B_167) ) ),
    inference(resolution,[status(thm)],[c_26,c_941])).

tff(c_1719,plain,(
    ! [D_221,B_222] :
      ( r2_hidden(D_221,a_2_1_orders_2(B_222,k1_xboole_0))
      | ~ m1_subset_1(D_221,u1_struct_0(B_222))
      | ~ l1_orders_2(B_222)
      | ~ v5_orders_2(B_222)
      | ~ v4_orders_2(B_222)
      | ~ v3_orders_2(B_222)
      | v2_struct_0(B_222) ) ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_967])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14696,plain,(
    ! [A_734,B_735] :
      ( r1_tarski(A_734,a_2_1_orders_2(B_735,k1_xboole_0))
      | ~ m1_subset_1('#skF_1'(A_734,a_2_1_orders_2(B_735,k1_xboole_0)),u1_struct_0(B_735))
      | ~ l1_orders_2(B_735)
      | ~ v5_orders_2(B_735)
      | ~ v4_orders_2(B_735)
      | ~ v3_orders_2(B_735)
      | v2_struct_0(B_735) ) ),
    inference(resolution,[status(thm)],[c_1719,c_4])).

tff(c_15161,plain,(
    ! [B_744] :
      ( ~ l1_orders_2(B_744)
      | ~ v5_orders_2(B_744)
      | ~ v4_orders_2(B_744)
      | ~ v3_orders_2(B_744)
      | v2_struct_0(B_744)
      | v1_xboole_0(u1_struct_0(B_744))
      | r1_tarski(u1_struct_0(B_744),a_2_1_orders_2(B_744,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_159,c_14696])).

tff(c_52,plain,(
    ! [A_35] :
      ( l1_struct_0(A_35)
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_82,plain,(
    ! [A_53] :
      ( k1_struct_0(A_53) = k1_xboole_0
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_87,plain,(
    ! [A_54] :
      ( k1_struct_0(A_54) = k1_xboole_0
      | ~ l1_orders_2(A_54) ) ),
    inference(resolution,[status(thm)],[c_52,c_82])).

tff(c_91,plain,(
    k1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_87])).

tff(c_66,plain,(
    k2_orders_2('#skF_5',k1_struct_0('#skF_5')) != u1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_92,plain,(
    k2_orders_2('#skF_5',k1_xboole_0) != u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_66])).

tff(c_1362,plain,(
    a_2_1_orders_2('#skF_5',k1_xboole_0) != u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_92])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_21,C_23,B_22] :
      ( m1_subset_1(A_21,C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(C_23))
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1418,plain,(
    ! [A_213] :
      ( m1_subset_1(A_213,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_213,a_2_1_orders_2('#skF_5',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1371,c_40])).

tff(c_1690,plain,(
    ! [B_220] :
      ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5',k1_xboole_0),B_220),u1_struct_0('#skF_5'))
      | r1_tarski(a_2_1_orders_2('#skF_5',k1_xboole_0),B_220) ) ),
    inference(resolution,[status(thm)],[c_6,c_1418])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_114,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden('#skF_1'(A_63,B_64),B_64)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_63,B_20] :
      ( r1_tarski(A_63,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1('#skF_1'(A_63,B_20),B_20) ) ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_1694,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | r1_tarski(a_2_1_orders_2('#skF_5',k1_xboole_0),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1690,c_119])).

tff(c_1700,plain,(
    r1_tarski(a_2_1_orders_2('#skF_5',k1_xboole_0),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1416,c_1694])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1710,plain,
    ( a_2_1_orders_2('#skF_5',k1_xboole_0) = u1_struct_0('#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_5'),a_2_1_orders_2('#skF_5',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1700,c_10])).

tff(c_1718,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),a_2_1_orders_2('#skF_5',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_1362,c_1710])).

tff(c_15204,plain,
    ( ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_15161,c_1718])).

tff(c_15259,plain,
    ( v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_15204])).

tff(c_15261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1416,c_76,c_15259])).

tff(c_15263,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(B_10,A_9)
      | ~ v1_xboole_0(B_10)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_15302,plain,(
    ! [A_748] : ~ r2_hidden(A_748,a_2_1_orders_2('#skF_5',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_15348,plain,(
    ! [B_749] : r1_tarski(a_2_1_orders_2('#skF_5',k1_xboole_0),B_749) ),
    inference(resolution,[status(thm)],[c_6,c_15302])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_125])).

tff(c_15415,plain,(
    a_2_1_orders_2('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15348,c_134])).

tff(c_15490,plain,(
    ! [D_750,B_751] :
      ( r2_hidden(D_750,a_2_1_orders_2(B_751,k1_xboole_0))
      | ~ m1_subset_1(D_750,u1_struct_0(B_751))
      | ~ l1_orders_2(B_751)
      | ~ v5_orders_2(B_751)
      | ~ v4_orders_2(B_751)
      | ~ v3_orders_2(B_751)
      | v2_struct_0(B_751) ) ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_967])).

tff(c_15512,plain,(
    ! [D_750] :
      ( r2_hidden(D_750,k1_xboole_0)
      | ~ m1_subset_1(D_750,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15415,c_15490])).

tff(c_15523,plain,(
    ! [D_750] :
      ( r2_hidden(D_750,k1_xboole_0)
      | ~ m1_subset_1(D_750,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_15512])).

tff(c_15525,plain,(
    ! [D_752] : ~ m1_subset_1(D_752,u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_209,c_15523])).

tff(c_15561,plain,(
    ! [B_10] :
      ( ~ v1_xboole_0(B_10)
      | ~ v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_22,c_15525])).

tff(c_15584,plain,(
    ! [B_10] : ~ v1_xboole_0(B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15263,c_15561])).

tff(c_15606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15584,c_15263])).

tff(c_15607,plain,(
    ! [A_11] : ~ v1_xboole_0(A_11) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_15614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15607,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n005.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 13:21:47 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.09/4.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.31  
% 11.09/4.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.31  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 11.09/4.31  
% 11.09/4.31  %Foreground sorts:
% 11.09/4.31  
% 11.09/4.31  
% 11.09/4.31  %Background operators:
% 11.09/4.31  
% 11.09/4.31  
% 11.09/4.31  %Foreground operators:
% 11.09/4.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.09/4.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 11.09/4.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.09/4.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.09/4.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.09/4.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.09/4.31  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 11.09/4.31  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 11.09/4.31  tff('#skF_5', type, '#skF_5': $i).
% 11.09/4.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.09/4.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 11.09/4.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 11.09/4.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.09/4.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.09/4.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 11.09/4.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 11.09/4.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.09/4.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.09/4.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.09/4.31  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 11.09/4.31  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 11.09/4.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.09/4.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.09/4.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.09/4.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.09/4.31  
% 11.09/4.33  tff(f_174, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_orders_2)).
% 11.09/4.33  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.09/4.33  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 11.09/4.33  tff(f_129, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 11.09/4.33  tff(f_89, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 11.09/4.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.09/4.33  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 11.09/4.33  tff(f_160, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 11.09/4.33  tff(f_133, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 11.09/4.33  tff(f_98, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 11.09/4.33  tff(f_82, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 11.09/4.33  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.09/4.33  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.09/4.33  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.09/4.33  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.09/4.33  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.09/4.33  tff(c_74, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.09/4.33  tff(c_72, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.09/4.33  tff(c_70, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.09/4.33  tff(c_68, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.09/4.33  tff(c_26, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.09/4.33  tff(c_271, plain, (![A_98, B_99]: (k2_orders_2(A_98, B_99)=a_2_1_orders_2(A_98, B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.09/4.33  tff(c_1354, plain, (![A_212]: (k2_orders_2(A_212, k1_xboole_0)=a_2_1_orders_2(A_212, k1_xboole_0) | ~l1_orders_2(A_212) | ~v5_orders_2(A_212) | ~v4_orders_2(A_212) | ~v3_orders_2(A_212) | v2_struct_0(A_212))), inference(resolution, [status(thm)], [c_26, c_271])).
% 11.09/4.33  tff(c_1357, plain, (k2_orders_2('#skF_5', k1_xboole_0)=a_2_1_orders_2('#skF_5', k1_xboole_0) | ~l1_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_1354])).
% 11.09/4.33  tff(c_1360, plain, (k2_orders_2('#skF_5', k1_xboole_0)=a_2_1_orders_2('#skF_5', k1_xboole_0) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_1357])).
% 11.09/4.33  tff(c_1361, plain, (k2_orders_2('#skF_5', k1_xboole_0)=a_2_1_orders_2('#skF_5', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_76, c_1360])).
% 11.09/4.33  tff(c_50, plain, (![A_33, B_34]: (m1_subset_1(k2_orders_2(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33) | ~v4_orders_2(A_33) | ~v3_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.09/4.33  tff(c_1366, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1361, c_50])).
% 11.09/4.33  tff(c_1370, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_26, c_1366])).
% 11.09/4.33  tff(c_1371, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1370])).
% 11.09/4.33  tff(c_42, plain, (![C_26, B_25, A_24]: (~v1_xboole_0(C_26) | ~m1_subset_1(B_25, k1_zfmisc_1(C_26)) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.09/4.33  tff(c_1404, plain, (![A_24]: (~v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden(A_24, a_2_1_orders_2('#skF_5', k1_xboole_0)))), inference(resolution, [status(thm)], [c_1371, c_42])).
% 11.09/4.33  tff(c_1416, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1404])).
% 11.09/4.33  tff(c_148, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.09/4.33  tff(c_18, plain, (![B_10, A_9]: (m1_subset_1(B_10, A_9) | ~r2_hidden(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.09/4.33  tff(c_159, plain, (![A_70, B_71]: (m1_subset_1('#skF_1'(A_70, B_71), A_70) | v1_xboole_0(A_70) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_148, c_18])).
% 11.09/4.33  tff(c_193, plain, (![C_80, B_81, A_82]: (~v1_xboole_0(C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.09/4.33  tff(c_200, plain, (![A_11, A_82]: (~v1_xboole_0(A_11) | ~r2_hidden(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_193])).
% 11.09/4.33  tff(c_209, plain, (![A_82]: (~r2_hidden(A_82, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_200])).
% 11.09/4.33  tff(c_941, plain, (![D_166, B_167, C_168]: (r2_hidden('#skF_4'(D_166, B_167, C_168, D_166), C_168) | r2_hidden(D_166, a_2_1_orders_2(B_167, C_168)) | ~m1_subset_1(D_166, u1_struct_0(B_167)) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(B_167))) | ~l1_orders_2(B_167) | ~v5_orders_2(B_167) | ~v4_orders_2(B_167) | ~v3_orders_2(B_167) | v2_struct_0(B_167))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.09/4.33  tff(c_967, plain, (![D_166, B_167]: (r2_hidden('#skF_4'(D_166, B_167, k1_xboole_0, D_166), k1_xboole_0) | r2_hidden(D_166, a_2_1_orders_2(B_167, k1_xboole_0)) | ~m1_subset_1(D_166, u1_struct_0(B_167)) | ~l1_orders_2(B_167) | ~v5_orders_2(B_167) | ~v4_orders_2(B_167) | ~v3_orders_2(B_167) | v2_struct_0(B_167))), inference(resolution, [status(thm)], [c_26, c_941])).
% 11.09/4.33  tff(c_1719, plain, (![D_221, B_222]: (r2_hidden(D_221, a_2_1_orders_2(B_222, k1_xboole_0)) | ~m1_subset_1(D_221, u1_struct_0(B_222)) | ~l1_orders_2(B_222) | ~v5_orders_2(B_222) | ~v4_orders_2(B_222) | ~v3_orders_2(B_222) | v2_struct_0(B_222))), inference(negUnitSimplification, [status(thm)], [c_209, c_967])).
% 11.09/4.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.09/4.33  tff(c_14696, plain, (![A_734, B_735]: (r1_tarski(A_734, a_2_1_orders_2(B_735, k1_xboole_0)) | ~m1_subset_1('#skF_1'(A_734, a_2_1_orders_2(B_735, k1_xboole_0)), u1_struct_0(B_735)) | ~l1_orders_2(B_735) | ~v5_orders_2(B_735) | ~v4_orders_2(B_735) | ~v3_orders_2(B_735) | v2_struct_0(B_735))), inference(resolution, [status(thm)], [c_1719, c_4])).
% 11.09/4.33  tff(c_15161, plain, (![B_744]: (~l1_orders_2(B_744) | ~v5_orders_2(B_744) | ~v4_orders_2(B_744) | ~v3_orders_2(B_744) | v2_struct_0(B_744) | v1_xboole_0(u1_struct_0(B_744)) | r1_tarski(u1_struct_0(B_744), a_2_1_orders_2(B_744, k1_xboole_0)))), inference(resolution, [status(thm)], [c_159, c_14696])).
% 11.09/4.33  tff(c_52, plain, (![A_35]: (l1_struct_0(A_35) | ~l1_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.09/4.33  tff(c_82, plain, (![A_53]: (k1_struct_0(A_53)=k1_xboole_0 | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.09/4.33  tff(c_87, plain, (![A_54]: (k1_struct_0(A_54)=k1_xboole_0 | ~l1_orders_2(A_54))), inference(resolution, [status(thm)], [c_52, c_82])).
% 11.09/4.33  tff(c_91, plain, (k1_struct_0('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_87])).
% 11.09/4.33  tff(c_66, plain, (k2_orders_2('#skF_5', k1_struct_0('#skF_5'))!=u1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.09/4.33  tff(c_92, plain, (k2_orders_2('#skF_5', k1_xboole_0)!=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_66])).
% 11.09/4.33  tff(c_1362, plain, (a_2_1_orders_2('#skF_5', k1_xboole_0)!=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_92])).
% 11.09/4.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.09/4.33  tff(c_40, plain, (![A_21, C_23, B_22]: (m1_subset_1(A_21, C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(C_23)) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.09/4.33  tff(c_1418, plain, (![A_213]: (m1_subset_1(A_213, u1_struct_0('#skF_5')) | ~r2_hidden(A_213, a_2_1_orders_2('#skF_5', k1_xboole_0)))), inference(resolution, [status(thm)], [c_1371, c_40])).
% 11.09/4.33  tff(c_1690, plain, (![B_220]: (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5', k1_xboole_0), B_220), u1_struct_0('#skF_5')) | r1_tarski(a_2_1_orders_2('#skF_5', k1_xboole_0), B_220))), inference(resolution, [status(thm)], [c_6, c_1418])).
% 11.09/4.33  tff(c_38, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.09/4.33  tff(c_114, plain, (![A_63, B_64]: (~r2_hidden('#skF_1'(A_63, B_64), B_64) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.09/4.33  tff(c_119, plain, (![A_63, B_20]: (r1_tarski(A_63, B_20) | v1_xboole_0(B_20) | ~m1_subset_1('#skF_1'(A_63, B_20), B_20))), inference(resolution, [status(thm)], [c_38, c_114])).
% 11.09/4.33  tff(c_1694, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | r1_tarski(a_2_1_orders_2('#skF_5', k1_xboole_0), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1690, c_119])).
% 11.09/4.33  tff(c_1700, plain, (r1_tarski(a_2_1_orders_2('#skF_5', k1_xboole_0), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1416, c_1694])).
% 11.09/4.33  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.09/4.33  tff(c_1710, plain, (a_2_1_orders_2('#skF_5', k1_xboole_0)=u1_struct_0('#skF_5') | ~r1_tarski(u1_struct_0('#skF_5'), a_2_1_orders_2('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_1700, c_10])).
% 11.09/4.33  tff(c_1718, plain, (~r1_tarski(u1_struct_0('#skF_5'), a_2_1_orders_2('#skF_5', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1362, c_1710])).
% 11.09/4.33  tff(c_15204, plain, (~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_15161, c_1718])).
% 11.09/4.33  tff(c_15259, plain, (v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_15204])).
% 11.09/4.33  tff(c_15261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1416, c_76, c_15259])).
% 11.09/4.33  tff(c_15263, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1404])).
% 11.09/4.33  tff(c_22, plain, (![B_10, A_9]: (m1_subset_1(B_10, A_9) | ~v1_xboole_0(B_10) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.09/4.33  tff(c_15302, plain, (![A_748]: (~r2_hidden(A_748, a_2_1_orders_2('#skF_5', k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1404])).
% 11.09/4.33  tff(c_15348, plain, (![B_749]: (r1_tarski(a_2_1_orders_2('#skF_5', k1_xboole_0), B_749))), inference(resolution, [status(thm)], [c_6, c_15302])).
% 11.09/4.33  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.09/4.33  tff(c_125, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.09/4.33  tff(c_134, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_125])).
% 11.09/4.33  tff(c_15415, plain, (a_2_1_orders_2('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_15348, c_134])).
% 11.09/4.33  tff(c_15490, plain, (![D_750, B_751]: (r2_hidden(D_750, a_2_1_orders_2(B_751, k1_xboole_0)) | ~m1_subset_1(D_750, u1_struct_0(B_751)) | ~l1_orders_2(B_751) | ~v5_orders_2(B_751) | ~v4_orders_2(B_751) | ~v3_orders_2(B_751) | v2_struct_0(B_751))), inference(negUnitSimplification, [status(thm)], [c_209, c_967])).
% 11.09/4.33  tff(c_15512, plain, (![D_750]: (r2_hidden(D_750, k1_xboole_0) | ~m1_subset_1(D_750, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15415, c_15490])).
% 11.09/4.33  tff(c_15523, plain, (![D_750]: (r2_hidden(D_750, k1_xboole_0) | ~m1_subset_1(D_750, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_15512])).
% 11.09/4.33  tff(c_15525, plain, (![D_752]: (~m1_subset_1(D_752, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_209, c_15523])).
% 11.09/4.33  tff(c_15561, plain, (![B_10]: (~v1_xboole_0(B_10) | ~v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_22, c_15525])).
% 11.09/4.33  tff(c_15584, plain, (![B_10]: (~v1_xboole_0(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_15263, c_15561])).
% 11.09/4.33  tff(c_15606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15584, c_15263])).
% 11.09/4.33  tff(c_15607, plain, (![A_11]: (~v1_xboole_0(A_11))), inference(splitRight, [status(thm)], [c_200])).
% 11.09/4.33  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.09/4.33  tff(c_15614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15607, c_8])).
% 11.09/4.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.33  
% 11.09/4.33  Inference rules
% 11.09/4.33  ----------------------
% 11.09/4.33  #Ref     : 0
% 11.09/4.33  #Sup     : 3552
% 11.09/4.33  #Fact    : 8
% 11.09/4.33  #Define  : 0
% 11.09/4.33  #Split   : 23
% 11.09/4.33  #Chain   : 0
% 11.09/4.33  #Close   : 0
% 11.09/4.33  
% 11.09/4.33  Ordering : KBO
% 11.09/4.33  
% 11.09/4.33  Simplification rules
% 11.09/4.33  ----------------------
% 11.09/4.33  #Subsume      : 1420
% 11.09/4.33  #Demod        : 1763
% 11.09/4.33  #Tautology    : 592
% 11.09/4.33  #SimpNegUnit  : 497
% 11.09/4.33  #BackRed      : 169
% 11.09/4.33  
% 11.09/4.33  #Partial instantiations: 0
% 11.09/4.33  #Strategies tried      : 1
% 11.09/4.33  
% 11.09/4.33  Timing (in seconds)
% 11.09/4.33  ----------------------
% 11.26/4.33  Preprocessing        : 0.35
% 11.26/4.33  Parsing              : 0.18
% 11.26/4.33  CNF conversion       : 0.03
% 11.26/4.33  Main loop            : 3.22
% 11.26/4.33  Inferencing          : 0.76
% 11.26/4.33  Reduction            : 0.90
% 11.26/4.33  Demodulation         : 0.60
% 11.26/4.33  BG Simplification    : 0.09
% 11.26/4.33  Subsumption          : 1.22
% 11.26/4.33  Abstraction          : 0.14
% 11.26/4.33  MUC search           : 0.00
% 11.26/4.33  Cooper               : 0.00
% 11.26/4.33  Total                : 3.61
% 11.26/4.33  Index Insertion      : 0.00
% 11.26/4.33  Index Deletion       : 0.00
% 11.26/4.33  Index Matching       : 0.00
% 11.26/4.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
