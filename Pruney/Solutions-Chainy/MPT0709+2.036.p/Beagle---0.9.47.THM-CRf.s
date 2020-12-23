%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:29 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 855 expanded)
%              Number of leaves         :   28 ( 292 expanded)
%              Depth                    :   21
%              Number of atoms          :  137 (1915 expanded)
%              Number of equality atoms :   59 ( 679 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_26,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_154,plain,(
    ! [B_41,A_42] :
      ( k1_relat_1(k7_relat_1(B_41,A_42)) = A_42
      | ~ r1_tarski(A_42,k1_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_160,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_154])).

tff(c_163,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_160])).

tff(c_73,plain,(
    ! [B_34,A_35] :
      ( k3_xboole_0(k1_relat_1(B_34),A_35) = k1_relat_1(k7_relat_1(B_34,A_35))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [B_34] :
      ( k1_relat_1(k7_relat_1(B_34,k1_relat_1(B_34))) = k1_relat_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_2])).

tff(c_176,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_80])).

tff(c_182,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_176])).

tff(c_184,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_187,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_187])).

tff(c_193,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(k1_relat_1(B_18),A_17) = k1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_17)) = k3_xboole_0('#skF_1',A_17)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_18])).

tff(c_194,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_194])).

tff(c_197,plain,(
    ! [A_17] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_17)) = k3_xboole_0('#skF_1',A_17) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,k3_xboole_0(k1_relat_1(B_16),A_15)) = k7_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_261,plain,(
    ! [A_46] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_46)) = k3_xboole_0('#skF_1',A_46) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_300,plain,(
    ! [A_15] :
      ( k3_xboole_0('#skF_1',k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),A_15)) = k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_15))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_261])).

tff(c_315,plain,(
    ! [A_15] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_1',A_15)) = k3_xboole_0('#skF_1',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_197,c_163,c_300])).

tff(c_8,plain,(
    ! [C_9,A_7,B_8] :
      ( k7_relat_1(k7_relat_1(C_9,A_7),B_8) = k7_relat_1(C_9,k3_xboole_0(A_7,B_8))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [B_37,A_38] :
      ( k7_relat_1(B_37,k3_xboole_0(k1_relat_1(B_37),A_38)) = k7_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_505,plain,(
    ! [B_59,A_60] :
      ( k7_relat_1(B_59,k1_relat_1(k7_relat_1(B_59,A_60))) = k7_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_108])).

tff(c_543,plain,(
    ! [A_17] :
      ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k3_xboole_0('#skF_1',A_17)) = k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_17)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_505])).

tff(c_609,plain,(
    ! [A_62] : k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k3_xboole_0('#skF_1',A_62)) = k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_193,c_543])).

tff(c_646,plain,(
    ! [A_62] :
      ( k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k3_xboole_0('#skF_1',A_62))) = k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_62)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_609])).

tff(c_668,plain,(
    ! [A_62] : k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_62) = k7_relat_1('#skF_2',k3_xboole_0('#skF_1',A_62)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_315,c_646])).

tff(c_134,plain,(
    ! [B_39,A_40] :
      ( k9_relat_1(B_39,k3_xboole_0(k1_relat_1(B_39),A_40)) = k9_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_460,plain,(
    ! [B_57,A_58] :
      ( k9_relat_1(B_57,k1_relat_1(k7_relat_1(B_57,A_58))) = k9_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_134])).

tff(c_475,plain,(
    ! [A_17] :
      ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),k3_xboole_0('#skF_1',A_17)) = k9_relat_1(k7_relat_1('#skF_2','#skF_1'),A_17)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_460])).

tff(c_497,plain,(
    ! [A_17] : k9_relat_1(k7_relat_1('#skF_2','#skF_1'),k3_xboole_0('#skF_1',A_17)) = k9_relat_1(k7_relat_1('#skF_2','#skF_1'),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_193,c_475])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_630,plain,(
    ! [A_62] :
      ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),k3_xboole_0('#skF_1',A_62)) = k2_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_62))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_12])).

tff(c_662,plain,(
    ! [A_62] : k2_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_62)) = k9_relat_1(k7_relat_1('#skF_2','#skF_1'),A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_497,c_630])).

tff(c_863,plain,(
    ! [A_71] : k2_relat_1(k7_relat_1('#skF_2',k3_xboole_0('#skF_1',A_71))) = k9_relat_1(k7_relat_1('#skF_2','#skF_1'),A_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_662])).

tff(c_869,plain,(
    ! [A_71] :
      ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),A_71) = k9_relat_1('#skF_2',k3_xboole_0('#skF_1',A_71))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_863,c_12])).

tff(c_910,plain,(
    ! [A_72] : k9_relat_1(k7_relat_1('#skF_2','#skF_1'),A_72) = k9_relat_1('#skF_2',k3_xboole_0('#skF_1',A_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_869])).

tff(c_889,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_863])).

tff(c_916,plain,(
    k9_relat_1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_889])).

tff(c_951,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_916])).

tff(c_14,plain,(
    ! [A_14] :
      ( k10_relat_1(A_14,k2_relat_1(A_14)) = k1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_977,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_14])).

tff(c_987,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_163,c_977])).

tff(c_377,plain,(
    ! [A_50,C_51,B_52] :
      ( k3_xboole_0(A_50,k10_relat_1(C_51,B_52)) = k10_relat_1(k7_relat_1(C_51,A_50),B_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1860,plain,(
    ! [C_91,B_92] :
      ( k3_xboole_0('#skF_1',k10_relat_1(k7_relat_1(C_91,'#skF_1'),B_92)) = k3_xboole_0('#skF_1',k10_relat_1(C_91,B_92))
      | ~ v1_relat_1(C_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_315])).

tff(c_1916,plain,
    ( k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k3_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_1860])).

tff(c_1950,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2,c_1916])).

tff(c_446,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k10_relat_1(B_55,k9_relat_1(B_55,A_56)),A_56)
      | ~ v2_funct_1(B_55)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(k7_relat_1(B_20,A_19)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_20])).

tff(c_375,plain,(
    ! [A_19] :
      ( k3_xboole_0('#skF_1',A_19) = A_19
      | ~ r1_tarski(A_19,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_197,c_167])).

tff(c_458,plain,(
    ! [B_55] :
      ( k3_xboole_0('#skF_1',k10_relat_1(B_55,k9_relat_1(B_55,'#skF_1'))) = k10_relat_1(B_55,k9_relat_1(B_55,'#skF_1'))
      | ~ v2_funct_1(B_55)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_446,c_375])).

tff(c_1974,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1950,c_458])).

tff(c_2004,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_1974])).

tff(c_2006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_2004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:05:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.63  
% 3.54/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.64  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 3.54/1.64  
% 3.54/1.64  %Foreground sorts:
% 3.54/1.64  
% 3.54/1.64  
% 3.54/1.64  %Background operators:
% 3.54/1.64  
% 3.54/1.64  
% 3.54/1.64  %Foreground operators:
% 3.54/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.54/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.54/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.54/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.54/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.54/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.64  
% 3.54/1.65  tff(f_88, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 3.54/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.54/1.65  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.54/1.65  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.54/1.65  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.54/1.65  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 3.54/1.65  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 3.54/1.65  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 3.54/1.65  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.54/1.65  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.54/1.65  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.54/1.65  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 3.54/1.65  tff(c_26, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.65  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.65  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.65  tff(c_28, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.65  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.65  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.65  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.65  tff(c_154, plain, (![B_41, A_42]: (k1_relat_1(k7_relat_1(B_41, A_42))=A_42 | ~r1_tarski(A_42, k1_relat_1(B_41)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.65  tff(c_160, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_154])).
% 3.54/1.65  tff(c_163, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_160])).
% 3.54/1.65  tff(c_73, plain, (![B_34, A_35]: (k3_xboole_0(k1_relat_1(B_34), A_35)=k1_relat_1(k7_relat_1(B_34, A_35)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.54/1.65  tff(c_80, plain, (![B_34]: (k1_relat_1(k7_relat_1(B_34, k1_relat_1(B_34)))=k1_relat_1(B_34) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_73, c_2])).
% 3.54/1.65  tff(c_176, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_80])).
% 3.54/1.65  tff(c_182, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_176])).
% 3.54/1.65  tff(c_184, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_182])).
% 3.54/1.65  tff(c_187, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_184])).
% 3.54/1.65  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_187])).
% 3.54/1.65  tff(c_193, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_182])).
% 3.54/1.65  tff(c_18, plain, (![B_18, A_17]: (k3_xboole_0(k1_relat_1(B_18), A_17)=k1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.54/1.65  tff(c_179, plain, (![A_17]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_17))=k3_xboole_0('#skF_1', A_17) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_18])).
% 3.54/1.65  tff(c_194, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_179])).
% 3.54/1.65  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_194])).
% 3.54/1.65  tff(c_197, plain, (![A_17]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_17))=k3_xboole_0('#skF_1', A_17))), inference(splitRight, [status(thm)], [c_179])).
% 3.54/1.65  tff(c_16, plain, (![B_16, A_15]: (k7_relat_1(B_16, k3_xboole_0(k1_relat_1(B_16), A_15))=k7_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.54/1.65  tff(c_261, plain, (![A_46]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_46))=k3_xboole_0('#skF_1', A_46))), inference(splitRight, [status(thm)], [c_179])).
% 3.54/1.65  tff(c_300, plain, (![A_15]: (k3_xboole_0('#skF_1', k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), A_15))=k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_15)) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16, c_261])).
% 3.54/1.65  tff(c_315, plain, (![A_15]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', A_15))=k3_xboole_0('#skF_1', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_197, c_163, c_300])).
% 3.54/1.65  tff(c_8, plain, (![C_9, A_7, B_8]: (k7_relat_1(k7_relat_1(C_9, A_7), B_8)=k7_relat_1(C_9, k3_xboole_0(A_7, B_8)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.65  tff(c_108, plain, (![B_37, A_38]: (k7_relat_1(B_37, k3_xboole_0(k1_relat_1(B_37), A_38))=k7_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.54/1.65  tff(c_505, plain, (![B_59, A_60]: (k7_relat_1(B_59, k1_relat_1(k7_relat_1(B_59, A_60)))=k7_relat_1(B_59, A_60) | ~v1_relat_1(B_59) | ~v1_relat_1(B_59))), inference(superposition, [status(thm), theory('equality')], [c_18, c_108])).
% 3.54/1.65  tff(c_543, plain, (![A_17]: (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k3_xboole_0('#skF_1', A_17))=k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_17) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_197, c_505])).
% 3.54/1.65  tff(c_609, plain, (![A_62]: (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k3_xboole_0('#skF_1', A_62))=k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_193, c_543])).
% 3.54/1.65  tff(c_646, plain, (![A_62]: (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', A_62)))=k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_62) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_609])).
% 3.54/1.65  tff(c_668, plain, (![A_62]: (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_62)=k7_relat_1('#skF_2', k3_xboole_0('#skF_1', A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_315, c_646])).
% 3.54/1.65  tff(c_134, plain, (![B_39, A_40]: (k9_relat_1(B_39, k3_xboole_0(k1_relat_1(B_39), A_40))=k9_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.65  tff(c_460, plain, (![B_57, A_58]: (k9_relat_1(B_57, k1_relat_1(k7_relat_1(B_57, A_58)))=k9_relat_1(B_57, A_58) | ~v1_relat_1(B_57) | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_18, c_134])).
% 3.54/1.65  tff(c_475, plain, (![A_17]: (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), k3_xboole_0('#skF_1', A_17))=k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_17) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_197, c_460])).
% 3.54/1.65  tff(c_497, plain, (![A_17]: (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), k3_xboole_0('#skF_1', A_17))=k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_193, c_475])).
% 3.54/1.65  tff(c_12, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.65  tff(c_630, plain, (![A_62]: (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), k3_xboole_0('#skF_1', A_62))=k2_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_62)) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_609, c_12])).
% 3.54/1.65  tff(c_662, plain, (![A_62]: (k2_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_62))=k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_497, c_630])).
% 3.54/1.65  tff(c_863, plain, (![A_71]: (k2_relat_1(k7_relat_1('#skF_2', k3_xboole_0('#skF_1', A_71)))=k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_71))), inference(demodulation, [status(thm), theory('equality')], [c_668, c_662])).
% 3.54/1.65  tff(c_869, plain, (![A_71]: (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_71)=k9_relat_1('#skF_2', k3_xboole_0('#skF_1', A_71)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_863, c_12])).
% 3.54/1.65  tff(c_910, plain, (![A_72]: (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_72)=k9_relat_1('#skF_2', k3_xboole_0('#skF_1', A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_869])).
% 3.54/1.65  tff(c_889, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_863])).
% 3.54/1.65  tff(c_916, plain, (k9_relat_1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_910, c_889])).
% 3.54/1.65  tff(c_951, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_916])).
% 3.54/1.65  tff(c_14, plain, (![A_14]: (k10_relat_1(A_14, k2_relat_1(A_14))=k1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.65  tff(c_977, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_951, c_14])).
% 3.54/1.65  tff(c_987, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_163, c_977])).
% 3.54/1.65  tff(c_377, plain, (![A_50, C_51, B_52]: (k3_xboole_0(A_50, k10_relat_1(C_51, B_52))=k10_relat_1(k7_relat_1(C_51, A_50), B_52) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.54/1.65  tff(c_1860, plain, (![C_91, B_92]: (k3_xboole_0('#skF_1', k10_relat_1(k7_relat_1(C_91, '#skF_1'), B_92))=k3_xboole_0('#skF_1', k10_relat_1(C_91, B_92)) | ~v1_relat_1(C_91))), inference(superposition, [status(thm), theory('equality')], [c_377, c_315])).
% 3.54/1.65  tff(c_1916, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k3_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_987, c_1860])).
% 3.54/1.65  tff(c_1950, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2, c_1916])).
% 3.54/1.65  tff(c_446, plain, (![B_55, A_56]: (r1_tarski(k10_relat_1(B_55, k9_relat_1(B_55, A_56)), A_56) | ~v2_funct_1(B_55) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.54/1.65  tff(c_20, plain, (![B_20, A_19]: (k1_relat_1(k7_relat_1(B_20, A_19))=A_19 | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.65  tff(c_167, plain, (![A_19]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_19))=A_19 | ~r1_tarski(A_19, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_20])).
% 3.54/1.65  tff(c_375, plain, (![A_19]: (k3_xboole_0('#skF_1', A_19)=A_19 | ~r1_tarski(A_19, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_197, c_167])).
% 3.54/1.65  tff(c_458, plain, (![B_55]: (k3_xboole_0('#skF_1', k10_relat_1(B_55, k9_relat_1(B_55, '#skF_1')))=k10_relat_1(B_55, k9_relat_1(B_55, '#skF_1')) | ~v2_funct_1(B_55) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_446, c_375])).
% 3.54/1.65  tff(c_1974, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1950, c_458])).
% 3.54/1.65  tff(c_2004, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_1974])).
% 3.54/1.65  tff(c_2006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_2004])).
% 3.54/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.65  
% 3.54/1.65  Inference rules
% 3.54/1.65  ----------------------
% 3.54/1.65  #Ref     : 0
% 3.54/1.65  #Sup     : 454
% 3.54/1.65  #Fact    : 0
% 3.54/1.65  #Define  : 0
% 3.54/1.65  #Split   : 2
% 3.54/1.65  #Chain   : 0
% 3.54/1.65  #Close   : 0
% 3.54/1.65  
% 3.54/1.65  Ordering : KBO
% 3.54/1.65  
% 3.54/1.65  Simplification rules
% 3.54/1.65  ----------------------
% 3.54/1.65  #Subsume      : 14
% 3.54/1.65  #Demod        : 501
% 3.54/1.65  #Tautology    : 238
% 3.54/1.65  #SimpNegUnit  : 1
% 3.54/1.65  #BackRed      : 7
% 3.54/1.65  
% 3.54/1.65  #Partial instantiations: 0
% 3.54/1.65  #Strategies tried      : 1
% 3.54/1.65  
% 3.54/1.65  Timing (in seconds)
% 3.54/1.65  ----------------------
% 3.54/1.66  Preprocessing        : 0.31
% 3.54/1.66  Parsing              : 0.17
% 3.54/1.66  CNF conversion       : 0.02
% 3.54/1.66  Main loop            : 0.51
% 3.54/1.66  Inferencing          : 0.18
% 3.54/1.66  Reduction            : 0.19
% 3.54/1.66  Demodulation         : 0.15
% 3.54/1.66  BG Simplification    : 0.03
% 3.54/1.66  Subsumption          : 0.08
% 3.54/1.66  Abstraction          : 0.03
% 3.54/1.66  MUC search           : 0.00
% 3.54/1.66  Cooper               : 0.00
% 3.54/1.66  Total                : 0.86
% 3.54/1.66  Index Insertion      : 0.00
% 3.54/1.66  Index Deletion       : 0.00
% 3.54/1.66  Index Matching       : 0.00
% 3.54/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
