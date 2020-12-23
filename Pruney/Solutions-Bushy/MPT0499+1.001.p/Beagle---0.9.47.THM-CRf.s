%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0499+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:24 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k1_relat_1(B),A)
         => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(c_14,plain,(
    k7_relat_1('#skF_2','#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,k2_zfmisc_1(k1_relat_1(A_7),k2_relat_1(A_7)))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_41,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(k2_zfmisc_1(A_19,C_20),k2_zfmisc_1(B_21,C_20))
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_116,plain,(
    ! [A_34,B_35,C_36,A_37] :
      ( r1_tarski(A_34,k2_zfmisc_1(B_35,C_36))
      | ~ r1_tarski(A_34,k2_zfmisc_1(A_37,C_36))
      | ~ r1_tarski(A_37,B_35) ) ),
    inference(resolution,[status(thm)],[c_41,c_6])).

tff(c_129,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,k2_zfmisc_1(B_39,k2_relat_1(A_38)))
      | ~ r1_tarski(k1_relat_1(A_38),B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_8,c_116])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_405,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,k2_zfmisc_1(B_73,k2_relat_1(A_72))) = A_72
      | ~ r1_tarski(k1_relat_1(A_72),B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_129,c_10])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k3_xboole_0(B_11,k2_zfmisc_1(A_10,k2_relat_1(B_11))) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_459,plain,(
    ! [A_74,B_75] :
      ( k7_relat_1(A_74,B_75) = A_74
      | ~ v1_relat_1(A_74)
      | ~ r1_tarski(k1_relat_1(A_74),B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_12])).

tff(c_478,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_459])).

tff(c_485,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_478])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_485])).

%------------------------------------------------------------------------------
