%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0777+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:50 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k2_wellord1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7,D_9] : k3_xboole_0(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,D_9)) = k2_zfmisc_1(k3_xboole_0(A_6,B_7),k3_xboole_0(C_8,D_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k3_xboole_0(A_1,k2_zfmisc_1(B_3,B_3)) = k2_wellord1(A_1,B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    ! [A_17,B_18,C_19] : k3_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k3_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_24,B_25,C_26] :
      ( k3_xboole_0(A_24,k3_xboole_0(k2_zfmisc_1(B_25,B_25),C_26)) = k3_xboole_0(k2_wellord1(A_24,B_25),C_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_23])).

tff(c_398,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( k3_xboole_0(A_44,k2_zfmisc_1(k3_xboole_0(C_45,B_46),k3_xboole_0(C_45,D_47))) = k3_xboole_0(k2_wellord1(A_44,C_45),k2_zfmisc_1(B_46,D_47))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_661,plain,(
    ! [A_52,C_53,D_54] :
      ( k3_xboole_0(k2_wellord1(A_52,C_53),k2_zfmisc_1(D_54,D_54)) = k2_wellord1(A_52,k3_xboole_0(C_53,D_54))
      | ~ v1_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_2])).

tff(c_715,plain,(
    ! [A_55,C_56,D_57] :
      ( k2_wellord1(k2_wellord1(A_55,C_56),D_57) = k2_wellord1(A_55,k3_xboole_0(C_56,D_57))
      | ~ v1_relat_1(k2_wellord1(A_55,C_56))
      | ~ v1_relat_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_2])).

tff(c_719,plain,(
    ! [A_58,B_59,D_60] :
      ( k2_wellord1(k2_wellord1(A_58,B_59),D_60) = k2_wellord1(A_58,k3_xboole_0(B_59,D_60))
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_4,c_715])).

tff(c_10,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_731,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_10])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_731])).

%------------------------------------------------------------------------------
