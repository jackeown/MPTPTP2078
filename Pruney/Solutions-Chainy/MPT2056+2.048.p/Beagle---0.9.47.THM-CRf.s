%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:31 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 114 expanded)
%              Number of leaves         :   44 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  139 ( 274 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k3_mcart_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_123,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_87,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [A_59,B_60] :
      ( ~ r1_xboole_0(A_59,B_60)
      | k3_xboole_0(A_59,B_60) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_87])).

tff(c_109,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_149,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_149])).

tff(c_164,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_161])).

tff(c_78,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(k1_tarski(A_51),B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_81,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(B_52,k1_tarski(A_51))
      | r2_hidden(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_239,plain,(
    ! [B_72,A_73] :
      ( k3_xboole_0(B_72,k1_tarski(A_73)) = k1_xboole_0
      | r2_hidden(A_73,B_72) ) ),
    inference(resolution,[status(thm)],[c_81,c_93])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_252,plain,(
    ! [B_72,A_73] :
      ( k4_xboole_0(B_72,k1_tarski(A_73)) = k5_xboole_0(B_72,k1_xboole_0)
      | r2_hidden(A_73,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_10])).

tff(c_274,plain,(
    ! [B_72,A_73] :
      ( k4_xboole_0(B_72,k1_tarski(A_73)) = B_72
      | r2_hidden(A_73,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_252])).

tff(c_281,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_284,plain,(
    ! [C_76] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',C_76) = k4_xboole_0('#skF_4',C_76) ),
    inference(resolution,[status(thm)],[c_36,c_281])).

tff(c_380,plain,(
    ! [A_109,B_110] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))),B_110,k1_tarski(k1_xboole_0)) = k2_yellow19(A_109,k3_yellow19(A_109,k2_struct_0(A_109),B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109)))))
      | ~ v13_waybel_0(B_110,k3_yellow_1(k2_struct_0(A_109)))
      | ~ v2_waybel_0(B_110,k3_yellow_1(k2_struct_0(A_109)))
      | v1_xboole_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_382,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_380])).

tff(c_385,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_284,c_382])).

tff(c_386,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_385])).

tff(c_34,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_387,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_34])).

tff(c_395,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_387])).

tff(c_32,plain,(
    ! [C_42,B_40,A_36] :
      ( ~ v1_xboole_0(C_42)
      | ~ r2_hidden(C_42,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0(B_40,k3_yellow_1(A_36))
      | ~ v2_waybel_0(B_40,k3_yellow_1(A_36))
      | ~ v1_subset_1(B_40,u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0(B_40)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_397,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_36))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_36))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_395,c_32])).

tff(c_404,plain,(
    ! [A_36] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_36))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_36))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_397])).

tff(c_410,plain,(
    ! [A_113] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_113))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_113))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_113))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_113)))
      | v1_xboole_0(A_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_404])).

tff(c_413,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_410])).

tff(c_416,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_413])).

tff(c_26,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(k2_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_419,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_416,c_26])).

tff(c_422,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_419])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.77  
% 2.85/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.77  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k3_mcart_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.21/1.77  
% 3.21/1.77  %Foreground sorts:
% 3.21/1.77  
% 3.21/1.77  
% 3.21/1.77  %Background operators:
% 3.21/1.77  
% 3.21/1.77  
% 3.21/1.77  %Foreground operators:
% 3.21/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.77  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.21/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.77  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.21/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.77  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.21/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.77  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.21/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.77  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.21/1.77  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.21/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.21/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.21/1.77  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.21/1.77  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.77  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.21/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.21/1.77  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.21/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.77  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.21/1.77  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.21/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.21/1.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.21/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.77  
% 3.21/1.80  tff(f_143, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.21/1.80  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.21/1.80  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.21/1.80  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.21/1.80  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.21/1.80  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.21/1.80  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.21/1.80  tff(f_55, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.21/1.80  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.21/1.80  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.21/1.80  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.21/1.80  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.21/1.80  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.21/1.80  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.21/1.80  tff(c_46, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.21/1.80  tff(c_42, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.21/1.80  tff(c_40, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.21/1.80  tff(c_38, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.21/1.80  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.21/1.80  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.21/1.80  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.21/1.80  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.21/1.80  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.80  tff(c_20, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.80  tff(c_87, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.21/1.80  tff(c_93, plain, (![A_59, B_60]: (~r1_xboole_0(A_59, B_60) | k3_xboole_0(A_59, B_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_87])).
% 3.21/1.80  tff(c_109, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_93])).
% 3.21/1.80  tff(c_149, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.80  tff(c_161, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_109, c_149])).
% 3.21/1.80  tff(c_164, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_161])).
% 3.21/1.80  tff(c_78, plain, (![A_51, B_52]: (r1_xboole_0(k1_tarski(A_51), B_52) | r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.80  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.21/1.80  tff(c_81, plain, (![B_52, A_51]: (r1_xboole_0(B_52, k1_tarski(A_51)) | r2_hidden(A_51, B_52))), inference(resolution, [status(thm)], [c_78, c_4])).
% 3.21/1.80  tff(c_239, plain, (![B_72, A_73]: (k3_xboole_0(B_72, k1_tarski(A_73))=k1_xboole_0 | r2_hidden(A_73, B_72))), inference(resolution, [status(thm)], [c_81, c_93])).
% 3.21/1.80  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.80  tff(c_252, plain, (![B_72, A_73]: (k4_xboole_0(B_72, k1_tarski(A_73))=k5_xboole_0(B_72, k1_xboole_0) | r2_hidden(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_239, c_10])).
% 3.21/1.80  tff(c_274, plain, (![B_72, A_73]: (k4_xboole_0(B_72, k1_tarski(A_73))=B_72 | r2_hidden(A_73, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_252])).
% 3.21/1.80  tff(c_281, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.21/1.80  tff(c_284, plain, (![C_76]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', C_76)=k4_xboole_0('#skF_4', C_76))), inference(resolution, [status(thm)], [c_36, c_281])).
% 3.21/1.80  tff(c_380, plain, (![A_109, B_110]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))), B_110, k1_tarski(k1_xboole_0))=k2_yellow19(A_109, k3_yellow19(A_109, k2_struct_0(A_109), B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))))) | ~v13_waybel_0(B_110, k3_yellow_1(k2_struct_0(A_109))) | ~v2_waybel_0(B_110, k3_yellow_1(k2_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.80  tff(c_382, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_380])).
% 3.21/1.80  tff(c_385, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_284, c_382])).
% 3.21/1.80  tff(c_386, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_385])).
% 3.21/1.80  tff(c_34, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.21/1.80  tff(c_387, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_386, c_34])).
% 3.21/1.80  tff(c_395, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_274, c_387])).
% 3.21/1.80  tff(c_32, plain, (![C_42, B_40, A_36]: (~v1_xboole_0(C_42) | ~r2_hidden(C_42, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0(B_40, k3_yellow_1(A_36)) | ~v2_waybel_0(B_40, k3_yellow_1(A_36)) | ~v1_subset_1(B_40, u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0(B_40) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.21/1.80  tff(c_397, plain, (![A_36]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_36)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_36)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_395, c_32])).
% 3.21/1.80  tff(c_404, plain, (![A_36]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_36)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_36)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_397])).
% 3.21/1.80  tff(c_410, plain, (![A_113]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_113)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_113)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_113)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_113))) | v1_xboole_0(A_113))), inference(negUnitSimplification, [status(thm)], [c_44, c_404])).
% 3.21/1.80  tff(c_413, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_410])).
% 3.21/1.80  tff(c_416, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_413])).
% 3.21/1.80  tff(c_26, plain, (![A_31]: (~v1_xboole_0(k2_struct_0(A_31)) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.21/1.80  tff(c_419, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_416, c_26])).
% 3.21/1.80  tff(c_422, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_419])).
% 3.21/1.80  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_422])).
% 3.21/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.80  
% 3.21/1.80  Inference rules
% 3.21/1.80  ----------------------
% 3.21/1.80  #Ref     : 0
% 3.21/1.80  #Sup     : 80
% 3.21/1.80  #Fact    : 0
% 3.21/1.80  #Define  : 0
% 3.21/1.80  #Split   : 2
% 3.21/1.80  #Chain   : 0
% 3.21/1.80  #Close   : 0
% 3.21/1.80  
% 3.21/1.80  Ordering : KBO
% 3.21/1.80  
% 3.21/1.80  Simplification rules
% 3.21/1.80  ----------------------
% 3.21/1.80  #Subsume      : 6
% 3.21/1.80  #Demod        : 22
% 3.21/1.80  #Tautology    : 47
% 3.21/1.80  #SimpNegUnit  : 16
% 3.21/1.80  #BackRed      : 1
% 3.21/1.80  
% 3.21/1.80  #Partial instantiations: 0
% 3.21/1.80  #Strategies tried      : 1
% 3.21/1.80  
% 3.21/1.80  Timing (in seconds)
% 3.21/1.80  ----------------------
% 3.21/1.81  Preprocessing        : 0.55
% 3.21/1.81  Parsing              : 0.29
% 3.21/1.81  CNF conversion       : 0.04
% 3.21/1.81  Main loop            : 0.40
% 3.21/1.81  Inferencing          : 0.16
% 3.21/1.81  Reduction            : 0.12
% 3.21/1.81  Demodulation         : 0.09
% 3.21/1.81  BG Simplification    : 0.03
% 3.21/1.81  Subsumption          : 0.07
% 3.21/1.81  Abstraction          : 0.03
% 3.21/1.81  MUC search           : 0.00
% 3.21/1.81  Cooper               : 0.00
% 3.21/1.81  Total                : 1.01
% 3.21/1.81  Index Insertion      : 0.00
% 3.21/1.81  Index Deletion       : 0.00
% 3.21/1.81  Index Matching       : 0.00
% 3.21/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
