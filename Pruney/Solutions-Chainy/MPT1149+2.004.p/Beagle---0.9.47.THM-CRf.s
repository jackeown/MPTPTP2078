%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:23 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 166 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  189 ( 501 expanded)
%              Number of equality atoms :   18 (  62 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_orders_2)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,B)
               => r2_hidden(D,C) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_14,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_139,plain,(
    ! [A_71,B_72] :
      ( k1_orders_2(A_71,B_72) = a_2_0_orders_2(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_orders_2(A_71)
      | ~ v5_orders_2(A_71)
      | ~ v4_orders_2(A_71)
      | ~ v3_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_155,plain,(
    ! [A_73] :
      ( k1_orders_2(A_73,k1_xboole_0) = a_2_0_orders_2(A_73,k1_xboole_0)
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_14,c_139])).

tff(c_158,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0)
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_155])).

tff(c_161,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_158])).

tff(c_162,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_161])).

tff(c_30,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    ! [A_43] :
      ( k1_struct_0(A_43) = k1_xboole_0
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    ! [A_44] :
      ( k1_struct_0(A_44) = k1_xboole_0
      | ~ l1_orders_2(A_44) ) ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_69,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_44,plain,(
    k1_orders_2('#skF_4',k1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_70,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_44])).

tff(c_163,plain,(
    a_2_0_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70])).

tff(c_168,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k1_orders_2(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_179,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_168])).

tff(c_184,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_14,c_179])).

tff(c_185,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_184])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_199,plain,(
    r1_tarski(a_2_0_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_185,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,
    ( a_2_0_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_199,c_2])).

tff(c_204,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_201])).

tff(c_12,plain,(
    ! [A_4,B_5,C_9] :
      ( m1_subset_1('#skF_1'(A_4,B_5,C_9),B_5)
      | r1_tarski(B_5,C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_350,plain,(
    ! [D_89,B_90,C_91] :
      ( r2_hidden('#skF_3'(D_89,B_90,C_91,D_89),C_91)
      | r2_hidden(D_89,a_2_0_orders_2(B_90,C_91))
      | ~ m1_subset_1(D_89,u1_struct_0(B_90))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(B_90)))
      | ~ l1_orders_2(B_90)
      | ~ v5_orders_2(B_90)
      | ~ v4_orders_2(B_90)
      | ~ v3_orders_2(B_90)
      | v2_struct_0(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1001,plain,(
    ! [D_134,B_135] :
      ( r2_hidden('#skF_3'(D_134,B_135,k1_xboole_0,D_134),k1_xboole_0)
      | r2_hidden(D_134,a_2_0_orders_2(B_135,k1_xboole_0))
      | ~ m1_subset_1(D_134,u1_struct_0(B_135))
      | ~ l1_orders_2(B_135)
      | ~ v5_orders_2(B_135)
      | ~ v4_orders_2(B_135)
      | ~ v3_orders_2(B_135)
      | v2_struct_0(B_135) ) ),
    inference(resolution,[status(thm)],[c_14,c_350])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1011,plain,(
    ! [D_134,B_135] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'(D_134,B_135,k1_xboole_0,D_134))
      | r2_hidden(D_134,a_2_0_orders_2(B_135,k1_xboole_0))
      | ~ m1_subset_1(D_134,u1_struct_0(B_135))
      | ~ l1_orders_2(B_135)
      | ~ v5_orders_2(B_135)
      | ~ v4_orders_2(B_135)
      | ~ v3_orders_2(B_135)
      | v2_struct_0(B_135) ) ),
    inference(resolution,[status(thm)],[c_1001,c_22])).

tff(c_1022,plain,(
    ! [D_136,B_137] :
      ( r2_hidden(D_136,a_2_0_orders_2(B_137,k1_xboole_0))
      | ~ m1_subset_1(D_136,u1_struct_0(B_137))
      | ~ l1_orders_2(B_137)
      | ~ v5_orders_2(B_137)
      | ~ v4_orders_2(B_137)
      | ~ v3_orders_2(B_137)
      | v2_struct_0(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1011])).

tff(c_10,plain,(
    ! [A_4,B_5,C_9] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5,C_9),C_9)
      | r1_tarski(B_5,C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5259,plain,(
    ! [B_330,B_331,A_332] :
      ( r1_tarski(B_330,a_2_0_orders_2(B_331,k1_xboole_0))
      | ~ m1_subset_1(a_2_0_orders_2(B_331,k1_xboole_0),k1_zfmisc_1(A_332))
      | ~ m1_subset_1(B_330,k1_zfmisc_1(A_332))
      | ~ m1_subset_1('#skF_1'(A_332,B_330,a_2_0_orders_2(B_331,k1_xboole_0)),u1_struct_0(B_331))
      | ~ l1_orders_2(B_331)
      | ~ v5_orders_2(B_331)
      | ~ v4_orders_2(B_331)
      | ~ v3_orders_2(B_331)
      | v2_struct_0(B_331) ) ),
    inference(resolution,[status(thm)],[c_1022,c_10])).

tff(c_5265,plain,(
    ! [B_333,A_334] :
      ( ~ l1_orders_2(B_333)
      | ~ v5_orders_2(B_333)
      | ~ v4_orders_2(B_333)
      | ~ v3_orders_2(B_333)
      | v2_struct_0(B_333)
      | r1_tarski(u1_struct_0(B_333),a_2_0_orders_2(B_333,k1_xboole_0))
      | ~ m1_subset_1(a_2_0_orders_2(B_333,k1_xboole_0),k1_zfmisc_1(A_334))
      | ~ m1_subset_1(u1_struct_0(B_333),k1_zfmisc_1(A_334)) ) ),
    inference(resolution,[status(thm)],[c_12,c_5259])).

tff(c_5269,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_185,c_5265])).

tff(c_5276,plain,
    ( v2_struct_0('#skF_4')
    | r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_5269])).

tff(c_5277,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_54,c_5276])).

tff(c_5281,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_5277])).

tff(c_5285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.66/2.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/2.67  
% 7.81/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/2.68  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 7.81/2.68  
% 7.81/2.68  %Foreground sorts:
% 7.81/2.68  
% 7.81/2.68  
% 7.81/2.68  %Background operators:
% 7.81/2.68  
% 7.81/2.68  
% 7.81/2.68  %Foreground operators:
% 7.81/2.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.81/2.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.81/2.68  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.81/2.68  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 7.81/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.81/2.68  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 7.81/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.81/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.81/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.81/2.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.81/2.68  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.81/2.68  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.81/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.81/2.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.81/2.68  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.81/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.81/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.81/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.81/2.68  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 7.81/2.68  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 7.81/2.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.81/2.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.81/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.81/2.68  
% 7.81/2.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.81/2.69  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.81/2.69  tff(f_142, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_orders_2)).
% 7.81/2.69  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.81/2.69  tff(f_82, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 7.81/2.69  tff(f_101, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 7.81/2.69  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 7.81/2.69  tff(f_97, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 7.81/2.69  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, B) => r2_hidden(D, C))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_subset_1)).
% 7.81/2.69  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.81/2.69  tff(f_128, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 7.81/2.69  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.81/2.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.81/2.69  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.81/2.69  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.81/2.69  tff(c_52, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.81/2.69  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.81/2.69  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.81/2.69  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.81/2.69  tff(c_14, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.81/2.69  tff(c_139, plain, (![A_71, B_72]: (k1_orders_2(A_71, B_72)=a_2_0_orders_2(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_orders_2(A_71) | ~v5_orders_2(A_71) | ~v4_orders_2(A_71) | ~v3_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.81/2.69  tff(c_155, plain, (![A_73]: (k1_orders_2(A_73, k1_xboole_0)=a_2_0_orders_2(A_73, k1_xboole_0) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_14, c_139])).
% 7.81/2.69  tff(c_158, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_155])).
% 7.81/2.69  tff(c_161, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_158])).
% 7.81/2.69  tff(c_162, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_161])).
% 7.81/2.69  tff(c_30, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.81/2.69  tff(c_60, plain, (![A_43]: (k1_struct_0(A_43)=k1_xboole_0 | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.81/2.69  tff(c_65, plain, (![A_44]: (k1_struct_0(A_44)=k1_xboole_0 | ~l1_orders_2(A_44))), inference(resolution, [status(thm)], [c_30, c_60])).
% 7.81/2.69  tff(c_69, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_65])).
% 7.81/2.69  tff(c_44, plain, (k1_orders_2('#skF_4', k1_struct_0('#skF_4'))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.81/2.69  tff(c_70, plain, (k1_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_44])).
% 7.81/2.69  tff(c_163, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70])).
% 7.81/2.69  tff(c_168, plain, (![A_74, B_75]: (m1_subset_1(k1_orders_2(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.81/2.69  tff(c_179, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_168])).
% 7.81/2.69  tff(c_184, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_14, c_179])).
% 7.81/2.69  tff(c_185, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_184])).
% 7.81/2.69  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.81/2.69  tff(c_199, plain, (r1_tarski(a_2_0_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_185, c_16])).
% 7.81/2.69  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.81/2.69  tff(c_201, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_199, c_2])).
% 7.81/2.69  tff(c_204, plain, (~r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_163, c_201])).
% 7.81/2.69  tff(c_12, plain, (![A_4, B_5, C_9]: (m1_subset_1('#skF_1'(A_4, B_5, C_9), B_5) | r1_tarski(B_5, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.81/2.69  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.81/2.69  tff(c_350, plain, (![D_89, B_90, C_91]: (r2_hidden('#skF_3'(D_89, B_90, C_91, D_89), C_91) | r2_hidden(D_89, a_2_0_orders_2(B_90, C_91)) | ~m1_subset_1(D_89, u1_struct_0(B_90)) | ~m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(B_90))) | ~l1_orders_2(B_90) | ~v5_orders_2(B_90) | ~v4_orders_2(B_90) | ~v3_orders_2(B_90) | v2_struct_0(B_90))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.81/2.69  tff(c_1001, plain, (![D_134, B_135]: (r2_hidden('#skF_3'(D_134, B_135, k1_xboole_0, D_134), k1_xboole_0) | r2_hidden(D_134, a_2_0_orders_2(B_135, k1_xboole_0)) | ~m1_subset_1(D_134, u1_struct_0(B_135)) | ~l1_orders_2(B_135) | ~v5_orders_2(B_135) | ~v4_orders_2(B_135) | ~v3_orders_2(B_135) | v2_struct_0(B_135))), inference(resolution, [status(thm)], [c_14, c_350])).
% 7.81/2.69  tff(c_22, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.81/2.69  tff(c_1011, plain, (![D_134, B_135]: (~r1_tarski(k1_xboole_0, '#skF_3'(D_134, B_135, k1_xboole_0, D_134)) | r2_hidden(D_134, a_2_0_orders_2(B_135, k1_xboole_0)) | ~m1_subset_1(D_134, u1_struct_0(B_135)) | ~l1_orders_2(B_135) | ~v5_orders_2(B_135) | ~v4_orders_2(B_135) | ~v3_orders_2(B_135) | v2_struct_0(B_135))), inference(resolution, [status(thm)], [c_1001, c_22])).
% 7.81/2.69  tff(c_1022, plain, (![D_136, B_137]: (r2_hidden(D_136, a_2_0_orders_2(B_137, k1_xboole_0)) | ~m1_subset_1(D_136, u1_struct_0(B_137)) | ~l1_orders_2(B_137) | ~v5_orders_2(B_137) | ~v4_orders_2(B_137) | ~v3_orders_2(B_137) | v2_struct_0(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1011])).
% 7.81/2.69  tff(c_10, plain, (![A_4, B_5, C_9]: (~r2_hidden('#skF_1'(A_4, B_5, C_9), C_9) | r1_tarski(B_5, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.81/2.69  tff(c_5259, plain, (![B_330, B_331, A_332]: (r1_tarski(B_330, a_2_0_orders_2(B_331, k1_xboole_0)) | ~m1_subset_1(a_2_0_orders_2(B_331, k1_xboole_0), k1_zfmisc_1(A_332)) | ~m1_subset_1(B_330, k1_zfmisc_1(A_332)) | ~m1_subset_1('#skF_1'(A_332, B_330, a_2_0_orders_2(B_331, k1_xboole_0)), u1_struct_0(B_331)) | ~l1_orders_2(B_331) | ~v5_orders_2(B_331) | ~v4_orders_2(B_331) | ~v3_orders_2(B_331) | v2_struct_0(B_331))), inference(resolution, [status(thm)], [c_1022, c_10])).
% 7.81/2.69  tff(c_5265, plain, (![B_333, A_334]: (~l1_orders_2(B_333) | ~v5_orders_2(B_333) | ~v4_orders_2(B_333) | ~v3_orders_2(B_333) | v2_struct_0(B_333) | r1_tarski(u1_struct_0(B_333), a_2_0_orders_2(B_333, k1_xboole_0)) | ~m1_subset_1(a_2_0_orders_2(B_333, k1_xboole_0), k1_zfmisc_1(A_334)) | ~m1_subset_1(u1_struct_0(B_333), k1_zfmisc_1(A_334)))), inference(resolution, [status(thm)], [c_12, c_5259])).
% 7.81/2.69  tff(c_5269, plain, (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_185, c_5265])).
% 7.81/2.69  tff(c_5276, plain, (v2_struct_0('#skF_4') | r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_5269])).
% 7.81/2.69  tff(c_5277, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_204, c_54, c_5276])).
% 7.81/2.69  tff(c_5281, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_5277])).
% 7.81/2.69  tff(c_5285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5281])).
% 7.81/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/2.69  
% 7.81/2.69  Inference rules
% 7.81/2.69  ----------------------
% 7.81/2.69  #Ref     : 0
% 7.81/2.69  #Sup     : 1104
% 7.81/2.69  #Fact    : 0
% 7.81/2.69  #Define  : 0
% 7.81/2.69  #Split   : 13
% 7.81/2.69  #Chain   : 0
% 7.81/2.69  #Close   : 0
% 7.81/2.69  
% 7.81/2.69  Ordering : KBO
% 7.81/2.69  
% 7.81/2.69  Simplification rules
% 7.81/2.69  ----------------------
% 7.81/2.69  #Subsume      : 196
% 7.81/2.69  #Demod        : 1965
% 7.81/2.69  #Tautology    : 179
% 7.81/2.69  #SimpNegUnit  : 337
% 7.81/2.69  #BackRed      : 4
% 7.81/2.69  
% 7.81/2.69  #Partial instantiations: 0
% 7.81/2.69  #Strategies tried      : 1
% 7.81/2.69  
% 7.81/2.69  Timing (in seconds)
% 7.81/2.69  ----------------------
% 7.81/2.69  Preprocessing        : 0.33
% 7.81/2.69  Parsing              : 0.17
% 7.81/2.69  CNF conversion       : 0.02
% 7.81/2.69  Main loop            : 1.57
% 7.81/2.69  Inferencing          : 0.46
% 7.81/2.69  Reduction            : 0.51
% 7.81/2.69  Demodulation         : 0.37
% 7.81/2.70  BG Simplification    : 0.05
% 7.81/2.70  Subsumption          : 0.47
% 7.81/2.70  Abstraction          : 0.08
% 7.81/2.70  MUC search           : 0.00
% 7.81/2.70  Cooper               : 0.00
% 7.81/2.70  Total                : 1.93
% 7.81/2.70  Index Insertion      : 0.00
% 7.81/2.70  Index Deletion       : 0.00
% 7.81/2.70  Index Matching       : 0.00
% 7.81/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
