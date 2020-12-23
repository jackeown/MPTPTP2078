%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0922+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:05 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 189 expanded)
%              Number of equality atoms :   63 ( 105 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = J ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k11_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).

tff(f_28,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_36,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

tff(c_12,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] :
      ( m1_subset_1(k10_mcart_1(A_1,B_2,C_3,D_4,E_5),C_3)
      | ~ m1_subset_1(E_5,k4_zfmisc_1(A_1,B_2,C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4,plain,(
    ! [B_7,D_9,C_8,E_10,A_6] :
      ( m1_subset_1(k11_mcart_1(A_6,B_7,C_8,D_9,E_10),D_9)
      | ~ m1_subset_1(E_10,k4_zfmisc_1(A_6,B_7,C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] :
      ( m1_subset_1(k8_mcart_1(A_11,B_12,C_13,D_14,E_15),A_11)
      | ~ m1_subset_1(E_15,k4_zfmisc_1(A_11,B_12,C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] :
      ( m1_subset_1(k9_mcart_1(A_16,B_17,C_18,D_19,E_20),B_17)
      | ~ m1_subset_1(E_20,k4_zfmisc_1(A_16,B_17,C_18,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    ! [E_83,A_81,C_84,B_85,D_82] :
      ( k4_mcart_1(k8_mcart_1(A_81,B_85,C_84,D_82,E_83),k9_mcart_1(A_81,B_85,C_84,D_82,E_83),k10_mcart_1(A_81,B_85,C_84,D_82,E_83),k11_mcart_1(A_81,B_85,C_84,D_82,E_83)) = E_83
      | ~ m1_subset_1(E_83,k4_zfmisc_1(A_81,B_85,C_84,D_82))
      | k1_xboole_0 = D_82
      | k1_xboole_0 = C_84
      | k1_xboole_0 = B_85
      | k1_xboole_0 = A_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [J_56,G_42,H_50,I_54] :
      ( J_56 = '#skF_5'
      | k4_mcart_1(G_42,H_50,I_54,J_56) != '#skF_6'
      | ~ m1_subset_1(J_56,'#skF_4')
      | ~ m1_subset_1(I_54,'#skF_3')
      | ~ m1_subset_1(H_50,'#skF_2')
      | ~ m1_subset_1(G_42,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    ! [A_87,E_90,B_89,D_86,C_88] :
      ( k11_mcart_1(A_87,B_89,C_88,D_86,E_90) = '#skF_5'
      | E_90 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1(A_87,B_89,C_88,D_86,E_90),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1(A_87,B_89,C_88,D_86,E_90),'#skF_3')
      | ~ m1_subset_1(k9_mcart_1(A_87,B_89,C_88,D_86,E_90),'#skF_2')
      | ~ m1_subset_1(k8_mcart_1(A_87,B_89,C_88,D_86,E_90),'#skF_1')
      | ~ m1_subset_1(E_90,k4_zfmisc_1(A_87,B_89,C_88,D_86))
      | k1_xboole_0 = D_86
      | k1_xboole_0 = C_88
      | k1_xboole_0 = B_89
      | k1_xboole_0 = A_87 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_54,plain,(
    ! [A_16,C_18,D_19,E_20] :
      ( k11_mcart_1(A_16,'#skF_2',C_18,D_19,E_20) = '#skF_5'
      | E_20 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1(A_16,'#skF_2',C_18,D_19,E_20),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1(A_16,'#skF_2',C_18,D_19,E_20),'#skF_3')
      | ~ m1_subset_1(k8_mcart_1(A_16,'#skF_2',C_18,D_19,E_20),'#skF_1')
      | k1_xboole_0 = D_19
      | k1_xboole_0 = C_18
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(E_20,k4_zfmisc_1(A_16,'#skF_2',C_18,D_19)) ) ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_59,plain,(
    ! [A_91,C_92,D_93,E_94] :
      ( k11_mcart_1(A_91,'#skF_2',C_92,D_93,E_94) = '#skF_5'
      | E_94 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1(A_91,'#skF_2',C_92,D_93,E_94),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1(A_91,'#skF_2',C_92,D_93,E_94),'#skF_3')
      | ~ m1_subset_1(k8_mcart_1(A_91,'#skF_2',C_92,D_93,E_94),'#skF_1')
      | k1_xboole_0 = D_93
      | k1_xboole_0 = C_92
      | k1_xboole_0 = A_91
      | ~ m1_subset_1(E_94,k4_zfmisc_1(A_91,'#skF_2',C_92,D_93)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_54])).

tff(c_63,plain,(
    ! [C_13,D_14,E_15] :
      ( k11_mcart_1('#skF_1','#skF_2',C_13,D_14,E_15) = '#skF_5'
      | E_15 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1('#skF_1','#skF_2',C_13,D_14,E_15),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2',C_13,D_14,E_15),'#skF_3')
      | k1_xboole_0 = D_14
      | k1_xboole_0 = C_13
      | k1_xboole_0 = '#skF_1'
      | ~ m1_subset_1(E_15,k4_zfmisc_1('#skF_1','#skF_2',C_13,D_14)) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_68,plain,(
    ! [C_95,D_96,E_97] :
      ( k11_mcart_1('#skF_1','#skF_2',C_95,D_96,E_97) = '#skF_5'
      | E_97 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1('#skF_1','#skF_2',C_95,D_96,E_97),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2',C_95,D_96,E_97),'#skF_3')
      | k1_xboole_0 = D_96
      | k1_xboole_0 = C_95
      | ~ m1_subset_1(E_97,k4_zfmisc_1('#skF_1','#skF_2',C_95,D_96)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_63])).

tff(c_72,plain,(
    ! [C_8,E_10] :
      ( k11_mcart_1('#skF_1','#skF_2',C_8,'#skF_4',E_10) = '#skF_5'
      | E_10 != '#skF_6'
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2',C_8,'#skF_4',E_10),'#skF_3')
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = C_8
      | ~ m1_subset_1(E_10,k4_zfmisc_1('#skF_1','#skF_2',C_8,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_77,plain,(
    ! [C_98,E_99] :
      ( k11_mcart_1('#skF_1','#skF_2',C_98,'#skF_4',E_99) = '#skF_5'
      | E_99 != '#skF_6'
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2',C_98,'#skF_4',E_99),'#skF_3')
      | k1_xboole_0 = C_98
      | ~ m1_subset_1(E_99,k4_zfmisc_1('#skF_1','#skF_2',C_98,'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_72])).

tff(c_81,plain,(
    ! [E_5] :
      ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4',E_5) = '#skF_5'
      | E_5 != '#skF_6'
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(E_5,k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_86,plain,(
    ! [E_100] :
      ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4',E_100) = '#skF_5'
      | E_100 != '#skF_6'
      | ~ m1_subset_1(E_100,k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_81])).

tff(c_105,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_105])).

%------------------------------------------------------------------------------
