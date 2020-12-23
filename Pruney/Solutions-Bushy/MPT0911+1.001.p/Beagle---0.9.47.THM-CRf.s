%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0911+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:04 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 136 expanded)
%              Number of equality atoms :   47 (  77 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_28,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_36,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_10,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k5_mcart_1(A_1,B_2,C_3,D_4),A_1)
      | ~ m1_subset_1(D_4,k3_zfmisc_1(A_1,B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( m1_subset_1(k6_mcart_1(A_5,B_6,C_7,D_8),B_6)
      | ~ m1_subset_1(D_8,k3_zfmisc_1(A_5,B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k7_mcart_1(A_9,B_10,C_11,D_12),C_11)
      | ~ m1_subset_1(D_12,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k3_mcart_1(k5_mcart_1(A_47,B_48,C_49,D_50),k6_mcart_1(A_47,B_48,C_49,D_50),k7_mcart_1(A_47,B_48,C_49,D_50)) = D_50
      | ~ m1_subset_1(D_50,k3_zfmisc_1(A_47,B_48,C_49))
      | k1_xboole_0 = C_49
      | k1_xboole_0 = B_48
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [H_31,F_25,G_29] :
      ( H_31 = '#skF_4'
      | k3_mcart_1(F_25,G_29,H_31) != '#skF_5'
      | ~ m1_subset_1(H_31,'#skF_3')
      | ~ m1_subset_1(G_29,'#skF_2')
      | ~ m1_subset_1(F_25,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k7_mcart_1(A_51,B_52,C_53,D_54) = '#skF_4'
      | D_54 != '#skF_5'
      | ~ m1_subset_1(k7_mcart_1(A_51,B_52,C_53,D_54),'#skF_3')
      | ~ m1_subset_1(k6_mcart_1(A_51,B_52,C_53,D_54),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_51,B_52,C_53,D_54),'#skF_1')
      | ~ m1_subset_1(D_54,k3_zfmisc_1(A_51,B_52,C_53))
      | k1_xboole_0 = C_53
      | k1_xboole_0 = B_52
      | k1_xboole_0 = A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_18])).

tff(c_47,plain,(
    ! [A_9,B_10,D_12] :
      ( k7_mcart_1(A_9,B_10,'#skF_3',D_12) = '#skF_4'
      | D_12 != '#skF_5'
      | ~ m1_subset_1(k6_mcart_1(A_9,B_10,'#skF_3',D_12),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_9,B_10,'#skF_3',D_12),'#skF_1')
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(D_12,k3_zfmisc_1(A_9,B_10,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_52,plain,(
    ! [A_55,B_56,D_57] :
      ( k7_mcart_1(A_55,B_56,'#skF_3',D_57) = '#skF_4'
      | D_57 != '#skF_5'
      | ~ m1_subset_1(k6_mcart_1(A_55,B_56,'#skF_3',D_57),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_55,B_56,'#skF_3',D_57),'#skF_1')
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55
      | ~ m1_subset_1(D_57,k3_zfmisc_1(A_55,B_56,'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_47])).

tff(c_56,plain,(
    ! [A_5,D_8] :
      ( k7_mcart_1(A_5,'#skF_2','#skF_3',D_8) = '#skF_4'
      | D_8 != '#skF_5'
      | ~ m1_subset_1(k5_mcart_1(A_5,'#skF_2','#skF_3',D_8),'#skF_1')
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = A_5
      | ~ m1_subset_1(D_8,k3_zfmisc_1(A_5,'#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_61,plain,(
    ! [A_58,D_59] :
      ( k7_mcart_1(A_58,'#skF_2','#skF_3',D_59) = '#skF_4'
      | D_59 != '#skF_5'
      | ~ m1_subset_1(k5_mcart_1(A_58,'#skF_2','#skF_3',D_59),'#skF_1')
      | k1_xboole_0 = A_58
      | ~ m1_subset_1(D_59,k3_zfmisc_1(A_58,'#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_56])).

tff(c_65,plain,(
    ! [D_4] :
      ( k7_mcart_1('#skF_1','#skF_2','#skF_3',D_4) = '#skF_4'
      | D_4 != '#skF_5'
      | k1_xboole_0 = '#skF_1'
      | ~ m1_subset_1(D_4,k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_70,plain,(
    ! [D_60] :
      ( k7_mcart_1('#skF_1','#skF_2','#skF_3',D_60) = '#skF_4'
      | D_60 != '#skF_5'
      | ~ m1_subset_1(D_60,k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_65])).

tff(c_85,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_85])).

%------------------------------------------------------------------------------
