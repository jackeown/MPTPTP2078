%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0356+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:10 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   32 (  52 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 ( 101 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_17,plain,(
    ! [A_10,B_11] :
      ( k3_subset_1(A_10,k3_subset_1(A_10,B_11)) = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_17])).

tff(c_92,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(k3_subset_1(A_16,C_17),k3_subset_1(A_16,B_18))
      | ~ r1_tarski(B_18,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [C_17] :
      ( r1_tarski(k3_subset_1('#skF_1',C_17),'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_92])).

tff(c_134,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_137,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_134])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_137])).

tff(c_143,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_107,plain,(
    ! [B_18] :
      ( r1_tarski('#skF_3',k3_subset_1('#skF_1',B_18))
      | ~ r1_tarski(B_18,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_18,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_92])).

tff(c_203,plain,(
    ! [B_25] :
      ( r1_tarski('#skF_3',k3_subset_1('#skF_1',B_25))
      | ~ r1_tarski(B_25,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_25,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_107])).

tff(c_208,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_214,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_208])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_214])).

%------------------------------------------------------------------------------
