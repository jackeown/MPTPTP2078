%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:27 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.27s
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
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_orders_2)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,B)
               => r2_hidden(D,C) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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
      ( k2_orders_2(A_71,B_72) = a_2_1_orders_2(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_orders_2(A_71)
      | ~ v5_orders_2(A_71)
      | ~ v4_orders_2(A_71)
      | ~ v3_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_155,plain,(
    ! [A_73] :
      ( k2_orders_2(A_73,k1_xboole_0) = a_2_1_orders_2(A_73,k1_xboole_0)
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_14,c_139])).

tff(c_158,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_155])).

tff(c_161,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_158])).

tff(c_162,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
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
    k2_orders_2('#skF_4',k1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_70,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_44])).

tff(c_163,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70])).

tff(c_168,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k2_orders_2(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_179,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_168])).

tff(c_184,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_14,c_179])).

tff(c_185,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_184])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_199,plain,(
    r1_tarski(a_2_1_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_185,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,
    ( a_2_1_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_4'),a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_199,c_2])).

tff(c_204,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
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
      | r2_hidden(D_89,a_2_1_orders_2(B_90,C_91))
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
      | r2_hidden(D_134,a_2_1_orders_2(B_135,k1_xboole_0))
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
      | r2_hidden(D_134,a_2_1_orders_2(B_135,k1_xboole_0))
      | ~ m1_subset_1(D_134,u1_struct_0(B_135))
      | ~ l1_orders_2(B_135)
      | ~ v5_orders_2(B_135)
      | ~ v4_orders_2(B_135)
      | ~ v3_orders_2(B_135)
      | v2_struct_0(B_135) ) ),
    inference(resolution,[status(thm)],[c_1001,c_22])).

tff(c_1022,plain,(
    ! [D_136,B_137] :
      ( r2_hidden(D_136,a_2_1_orders_2(B_137,k1_xboole_0))
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
      ( r1_tarski(B_330,a_2_1_orders_2(B_331,k1_xboole_0))
      | ~ m1_subset_1(a_2_1_orders_2(B_331,k1_xboole_0),k1_zfmisc_1(A_332))
      | ~ m1_subset_1(B_330,k1_zfmisc_1(A_332))
      | ~ m1_subset_1('#skF_1'(A_332,B_330,a_2_1_orders_2(B_331,k1_xboole_0)),u1_struct_0(B_331))
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
      | r1_tarski(u1_struct_0(B_333),a_2_1_orders_2(B_333,k1_xboole_0))
      | ~ m1_subset_1(a_2_1_orders_2(B_333,k1_xboole_0),k1_zfmisc_1(A_334))
      | ~ m1_subset_1(u1_struct_0(B_333),k1_zfmisc_1(A_334)) ) ),
    inference(resolution,[status(thm)],[c_12,c_5259])).

tff(c_5269,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | r1_tarski(u1_struct_0('#skF_4'),a_2_1_orders_2('#skF_4',k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_185,c_5265])).

tff(c_5276,plain,
    ( v2_struct_0('#skF_4')
    | r1_tarski(u1_struct_0('#skF_4'),a_2_1_orders_2('#skF_4',k1_xboole_0))
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
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.08/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.85  
% 8.08/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.85  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 8.08/2.85  
% 8.08/2.85  %Foreground sorts:
% 8.08/2.85  
% 8.08/2.85  
% 8.08/2.85  %Background operators:
% 8.08/2.85  
% 8.08/2.85  
% 8.08/2.85  %Foreground operators:
% 8.08/2.85  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.08/2.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.08/2.85  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.08/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.08/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.08/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.08/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.08/2.85  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 8.08/2.85  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 8.08/2.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.08/2.85  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.08/2.85  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 8.08/2.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.08/2.85  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.08/2.85  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.08/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.08/2.85  tff('#skF_4', type, '#skF_4': $i).
% 8.08/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.08/2.85  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 8.08/2.85  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 8.08/2.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.08/2.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.08/2.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.08/2.85  
% 8.27/2.87  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.27/2.87  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.27/2.87  tff(f_142, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_orders_2)).
% 8.27/2.87  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.27/2.87  tff(f_82, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 8.27/2.87  tff(f_101, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 8.27/2.87  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 8.27/2.87  tff(f_97, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 8.27/2.87  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, B) => r2_hidden(D, C))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_subset_1)).
% 8.27/2.87  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.27/2.87  tff(f_128, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 8.27/2.87  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.27/2.87  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.27/2.87  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.27/2.87  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.27/2.87  tff(c_52, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.27/2.87  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.27/2.87  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.27/2.87  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.27/2.87  tff(c_14, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.27/2.87  tff(c_139, plain, (![A_71, B_72]: (k2_orders_2(A_71, B_72)=a_2_1_orders_2(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_orders_2(A_71) | ~v5_orders_2(A_71) | ~v4_orders_2(A_71) | ~v3_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.27/2.87  tff(c_155, plain, (![A_73]: (k2_orders_2(A_73, k1_xboole_0)=a_2_1_orders_2(A_73, k1_xboole_0) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_14, c_139])).
% 8.27/2.87  tff(c_158, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_155])).
% 8.27/2.87  tff(c_161, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_158])).
% 8.27/2.87  tff(c_162, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_161])).
% 8.27/2.87  tff(c_30, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.27/2.87  tff(c_60, plain, (![A_43]: (k1_struct_0(A_43)=k1_xboole_0 | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.27/2.87  tff(c_65, plain, (![A_44]: (k1_struct_0(A_44)=k1_xboole_0 | ~l1_orders_2(A_44))), inference(resolution, [status(thm)], [c_30, c_60])).
% 8.27/2.87  tff(c_69, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_65])).
% 8.27/2.87  tff(c_44, plain, (k2_orders_2('#skF_4', k1_struct_0('#skF_4'))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.27/2.87  tff(c_70, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_44])).
% 8.27/2.87  tff(c_163, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70])).
% 8.27/2.87  tff(c_168, plain, (![A_74, B_75]: (m1_subset_1(k2_orders_2(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.27/2.87  tff(c_179, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_168])).
% 8.27/2.87  tff(c_184, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_14, c_179])).
% 8.27/2.87  tff(c_185, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_184])).
% 8.27/2.87  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.27/2.87  tff(c_199, plain, (r1_tarski(a_2_1_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_185, c_16])).
% 8.27/2.87  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.27/2.87  tff(c_201, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), a_2_1_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_199, c_2])).
% 8.27/2.87  tff(c_204, plain, (~r1_tarski(u1_struct_0('#skF_4'), a_2_1_orders_2('#skF_4', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_163, c_201])).
% 8.27/2.87  tff(c_12, plain, (![A_4, B_5, C_9]: (m1_subset_1('#skF_1'(A_4, B_5, C_9), B_5) | r1_tarski(B_5, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.27/2.87  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.27/2.87  tff(c_350, plain, (![D_89, B_90, C_91]: (r2_hidden('#skF_3'(D_89, B_90, C_91, D_89), C_91) | r2_hidden(D_89, a_2_1_orders_2(B_90, C_91)) | ~m1_subset_1(D_89, u1_struct_0(B_90)) | ~m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(B_90))) | ~l1_orders_2(B_90) | ~v5_orders_2(B_90) | ~v4_orders_2(B_90) | ~v3_orders_2(B_90) | v2_struct_0(B_90))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.27/2.87  tff(c_1001, plain, (![D_134, B_135]: (r2_hidden('#skF_3'(D_134, B_135, k1_xboole_0, D_134), k1_xboole_0) | r2_hidden(D_134, a_2_1_orders_2(B_135, k1_xboole_0)) | ~m1_subset_1(D_134, u1_struct_0(B_135)) | ~l1_orders_2(B_135) | ~v5_orders_2(B_135) | ~v4_orders_2(B_135) | ~v3_orders_2(B_135) | v2_struct_0(B_135))), inference(resolution, [status(thm)], [c_14, c_350])).
% 8.27/2.87  tff(c_22, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.27/2.87  tff(c_1011, plain, (![D_134, B_135]: (~r1_tarski(k1_xboole_0, '#skF_3'(D_134, B_135, k1_xboole_0, D_134)) | r2_hidden(D_134, a_2_1_orders_2(B_135, k1_xboole_0)) | ~m1_subset_1(D_134, u1_struct_0(B_135)) | ~l1_orders_2(B_135) | ~v5_orders_2(B_135) | ~v4_orders_2(B_135) | ~v3_orders_2(B_135) | v2_struct_0(B_135))), inference(resolution, [status(thm)], [c_1001, c_22])).
% 8.27/2.87  tff(c_1022, plain, (![D_136, B_137]: (r2_hidden(D_136, a_2_1_orders_2(B_137, k1_xboole_0)) | ~m1_subset_1(D_136, u1_struct_0(B_137)) | ~l1_orders_2(B_137) | ~v5_orders_2(B_137) | ~v4_orders_2(B_137) | ~v3_orders_2(B_137) | v2_struct_0(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1011])).
% 8.27/2.87  tff(c_10, plain, (![A_4, B_5, C_9]: (~r2_hidden('#skF_1'(A_4, B_5, C_9), C_9) | r1_tarski(B_5, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.27/2.87  tff(c_5259, plain, (![B_330, B_331, A_332]: (r1_tarski(B_330, a_2_1_orders_2(B_331, k1_xboole_0)) | ~m1_subset_1(a_2_1_orders_2(B_331, k1_xboole_0), k1_zfmisc_1(A_332)) | ~m1_subset_1(B_330, k1_zfmisc_1(A_332)) | ~m1_subset_1('#skF_1'(A_332, B_330, a_2_1_orders_2(B_331, k1_xboole_0)), u1_struct_0(B_331)) | ~l1_orders_2(B_331) | ~v5_orders_2(B_331) | ~v4_orders_2(B_331) | ~v3_orders_2(B_331) | v2_struct_0(B_331))), inference(resolution, [status(thm)], [c_1022, c_10])).
% 8.27/2.87  tff(c_5265, plain, (![B_333, A_334]: (~l1_orders_2(B_333) | ~v5_orders_2(B_333) | ~v4_orders_2(B_333) | ~v3_orders_2(B_333) | v2_struct_0(B_333) | r1_tarski(u1_struct_0(B_333), a_2_1_orders_2(B_333, k1_xboole_0)) | ~m1_subset_1(a_2_1_orders_2(B_333, k1_xboole_0), k1_zfmisc_1(A_334)) | ~m1_subset_1(u1_struct_0(B_333), k1_zfmisc_1(A_334)))), inference(resolution, [status(thm)], [c_12, c_5259])).
% 8.27/2.87  tff(c_5269, plain, (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(u1_struct_0('#skF_4'), a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_185, c_5265])).
% 8.27/2.87  tff(c_5276, plain, (v2_struct_0('#skF_4') | r1_tarski(u1_struct_0('#skF_4'), a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_5269])).
% 8.27/2.87  tff(c_5277, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_204, c_54, c_5276])).
% 8.27/2.87  tff(c_5281, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_5277])).
% 8.27/2.87  tff(c_5285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5281])).
% 8.27/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.27/2.87  
% 8.27/2.87  Inference rules
% 8.27/2.87  ----------------------
% 8.27/2.87  #Ref     : 0
% 8.27/2.87  #Sup     : 1104
% 8.27/2.87  #Fact    : 0
% 8.27/2.87  #Define  : 0
% 8.27/2.87  #Split   : 13
% 8.27/2.87  #Chain   : 0
% 8.27/2.87  #Close   : 0
% 8.27/2.87  
% 8.27/2.87  Ordering : KBO
% 8.27/2.87  
% 8.27/2.87  Simplification rules
% 8.27/2.87  ----------------------
% 8.27/2.87  #Subsume      : 196
% 8.27/2.87  #Demod        : 1965
% 8.27/2.87  #Tautology    : 179
% 8.27/2.87  #SimpNegUnit  : 337
% 8.27/2.87  #BackRed      : 4
% 8.27/2.87  
% 8.27/2.87  #Partial instantiations: 0
% 8.27/2.87  #Strategies tried      : 1
% 8.27/2.87  
% 8.27/2.87  Timing (in seconds)
% 8.27/2.87  ----------------------
% 8.27/2.87  Preprocessing        : 0.36
% 8.27/2.87  Parsing              : 0.20
% 8.27/2.87  CNF conversion       : 0.02
% 8.27/2.87  Main loop            : 1.68
% 8.27/2.87  Inferencing          : 0.50
% 8.27/2.87  Reduction            : 0.52
% 8.27/2.87  Demodulation         : 0.37
% 8.27/2.87  BG Simplification    : 0.07
% 8.27/2.87  Subsumption          : 0.51
% 8.27/2.87  Abstraction          : 0.08
% 8.27/2.87  MUC search           : 0.00
% 8.27/2.87  Cooper               : 0.00
% 8.27/2.87  Total                : 2.08
% 8.27/2.87  Index Insertion      : 0.00
% 8.27/2.88  Index Deletion       : 0.00
% 8.27/2.88  Index Matching       : 0.00
% 8.27/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
