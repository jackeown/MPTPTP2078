%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0353+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:09 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   57 (  90 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 117 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_102,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_111,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k3_subset_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_780,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,k3_subset_1(A_67,B_68)) = k3_subset_1(A_67,k3_subset_1(A_67,B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_786,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_780])).

tff(c_791,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_786])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,(
    ! [A_27,B_28,C_29] : k4_xboole_0(k3_xboole_0(A_27,B_28),C_29) = k3_xboole_0(A_27,k4_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    ! [A_10,C_29] : k3_xboole_0(A_10,k4_xboole_0(A_10,C_29)) = k4_xboole_0(A_10,C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_838,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_82])).

tff(c_842,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_838])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k3_xboole_0(A_20,B_21),C_22) = k3_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_850,plain,(
    ! [C_22] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_22)) = k4_xboole_0('#skF_2',C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_18])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_139,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_128])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_211,plain,(
    ! [B_44,A_45,C_46] : k4_xboole_0(k3_xboole_0(B_44,A_45),C_46) = k3_xboole_0(A_45,k4_xboole_0(B_44,C_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_255,plain,(
    ! [B_47,A_48,C_49] : k3_xboole_0(B_47,k4_xboole_0(A_48,C_49)) = k3_xboole_0(A_48,k4_xboole_0(B_47,C_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_211])).

tff(c_329,plain,(
    ! [A_48] : k3_xboole_0(A_48,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1',k4_xboole_0(A_48,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_255])).

tff(c_164,plain,(
    ! [A_38,B_39,C_40] :
      ( k9_subset_1(A_38,B_39,C_40) = k3_xboole_0(B_39,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_173,plain,(
    ! [B_39] : k9_subset_1('#skF_1',B_39,'#skF_2') = k3_xboole_0(B_39,'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_164])).

tff(c_610,plain,(
    ! [A_61,C_62,B_63] :
      ( k9_subset_1(A_61,C_62,B_63) = k9_subset_1(A_61,B_63,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_616,plain,(
    ! [B_63] : k9_subset_1('#skF_1',B_63,'#skF_2') = k9_subset_1('#skF_1','#skF_2',B_63) ),
    inference(resolution,[status(thm)],[c_24,c_610])).

tff(c_621,plain,(
    ! [B_63] : k9_subset_1('#skF_1','#skF_2',B_63) = k3_xboole_0(B_63,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_616])).

tff(c_401,plain,(
    ! [A_52,B_53,C_54] :
      ( k7_subset_1(A_52,B_53,C_54) = k4_xboole_0(B_53,C_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_410,plain,(
    ! [C_54] : k7_subset_1('#skF_1','#skF_2',C_54) = k4_xboole_0('#skF_2',C_54) ),
    inference(resolution,[status(thm)],[c_24,c_401])).

tff(c_20,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_420,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_20])).

tff(c_651,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_420])).

tff(c_652,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_651])).

tff(c_682,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_652])).

tff(c_1081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_682])).

%------------------------------------------------------------------------------
