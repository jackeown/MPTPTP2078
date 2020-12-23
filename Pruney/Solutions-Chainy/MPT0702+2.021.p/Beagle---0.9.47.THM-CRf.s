%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:05 EST 2020

% Result     : Theorem 13.48s
% Output     : CNFRefutation 13.74s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 249 expanded)
%              Number of leaves         :   38 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          :  174 ( 645 expanded)
%              Number of equality atoms :   43 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_275,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | k4_xboole_0(A_62,B_63) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_291,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_275,c_46])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_185,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_205,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_185])).

tff(c_306,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_321,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_306])).

tff(c_326,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_321])).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    ! [B_34,A_33] :
      ( k10_relat_1(k2_funct_1(B_34),A_33) = k9_relat_1(B_34,A_33)
      | ~ v2_funct_1(B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    ! [A_25] :
      ( v1_funct_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [A_25] :
      ( v1_relat_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    ! [A_24] :
      ( k10_relat_1(A_24,k2_relat_1(A_24)) = k1_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_580,plain,(
    ! [B_85,A_86] :
      ( k9_relat_1(k2_funct_1(B_85),A_86) = k10_relat_1(B_85,A_86)
      | ~ v2_funct_1(B_85)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k9_relat_1(B_23,A_22),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7464,plain,(
    ! [B_291,A_292] :
      ( r1_tarski(k10_relat_1(B_291,A_292),k2_relat_1(k2_funct_1(B_291)))
      | ~ v1_relat_1(k2_funct_1(B_291))
      | ~ v2_funct_1(B_291)
      | ~ v1_funct_1(B_291)
      | ~ v1_relat_1(B_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_28])).

tff(c_33316,plain,(
    ! [A_659] :
      ( r1_tarski(k1_relat_1(A_659),k2_relat_1(k2_funct_1(A_659)))
      | ~ v1_relat_1(k2_funct_1(A_659))
      | ~ v2_funct_1(A_659)
      | ~ v1_funct_1(A_659)
      | ~ v1_relat_1(A_659)
      | ~ v1_relat_1(A_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7464])).

tff(c_50,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_118,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_118])).

tff(c_353,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(k2_xboole_0(A_71,B_73),C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_360,plain,(
    ! [C_72] :
      ( r1_tarski('#skF_1',C_72)
      | ~ r1_tarski(k1_relat_1('#skF_3'),C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_353])).

tff(c_33345,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_33316,c_360])).

tff(c_33378,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_48,c_33345])).

tff(c_33383,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_33378])).

tff(c_33386,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_33383])).

tff(c_33390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_33386])).

tff(c_33392,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_33378])).

tff(c_33391,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_33378])).

tff(c_38,plain,(
    ! [B_30,A_29] :
      ( k9_relat_1(B_30,k10_relat_1(B_30,A_29)) = A_29
      | ~ r1_tarski(A_29,k2_relat_1(B_30))
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_33610,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_33391,c_38])).

tff(c_33628,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33392,c_33610])).

tff(c_41886,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_33628])).

tff(c_41889,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_41886])).

tff(c_41893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_41889])).

tff(c_41894,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_33628])).

tff(c_44,plain,(
    ! [B_36,A_35] :
      ( k9_relat_1(k2_funct_1(B_36),A_35) = k10_relat_1(B_36,A_35)
      | ~ v2_funct_1(B_36)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_41995,plain,
    ( k10_relat_1('#skF_3',k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_41894,c_44])).

tff(c_42076,plain,(
    k10_relat_1('#skF_3',k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_48,c_41995])).

tff(c_42109,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_42076])).

tff(c_42125,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_48,c_42109])).

tff(c_1791,plain,(
    ! [C_139,A_140,B_141] :
      ( k3_xboole_0(k9_relat_1(C_139,A_140),k9_relat_1(C_139,B_141)) = k9_relat_1(C_139,k3_xboole_0(A_140,B_141))
      | ~ v2_funct_1(C_139)
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_201,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_185])).

tff(c_1822,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1791,c_201])).

tff(c_1859,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_48,c_1822])).

tff(c_40,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k10_relat_1(B_32,k9_relat_1(B_32,A_31)),A_31)
      | ~ v2_funct_1(B_32)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1874,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1859,c_40])).

tff(c_1885,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_48,c_1874])).

tff(c_42148,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42125,c_1885])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_379,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_398,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,k3_xboole_0(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_18,c_379])).

tff(c_42325,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42148,c_398])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42599,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42325,c_12])).

tff(c_42682,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_42599])).

tff(c_42684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_42682])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:54:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.48/6.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.48/6.71  
% 13.48/6.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.48/6.71  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.48/6.71  
% 13.48/6.71  %Foreground sorts:
% 13.48/6.71  
% 13.48/6.71  
% 13.48/6.71  %Background operators:
% 13.48/6.71  
% 13.48/6.71  
% 13.48/6.71  %Foreground operators:
% 13.48/6.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.48/6.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.48/6.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.48/6.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.48/6.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.48/6.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.48/6.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.48/6.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.48/6.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.48/6.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.48/6.71  tff('#skF_2', type, '#skF_2': $i).
% 13.48/6.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.48/6.71  tff('#skF_3', type, '#skF_3': $i).
% 13.48/6.71  tff('#skF_1', type, '#skF_1': $i).
% 13.48/6.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.48/6.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.48/6.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.48/6.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.48/6.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.48/6.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.48/6.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.48/6.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.48/6.71  
% 13.74/6.73  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.74/6.73  tff(f_126, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 13.74/6.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.74/6.73  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.74/6.73  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.74/6.73  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 13.74/6.73  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.74/6.73  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 13.74/6.73  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 13.74/6.73  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 13.74/6.73  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.74/6.73  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 13.74/6.73  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 13.74/6.73  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 13.74/6.73  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 13.74/6.73  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.74/6.73  tff(c_275, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | k4_xboole_0(A_62, B_63)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.74/6.73  tff(c_46, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.74/6.73  tff(c_291, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_275, c_46])).
% 13.74/6.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.74/6.73  tff(c_68, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.74/6.73  tff(c_89, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_68])).
% 13.74/6.73  tff(c_185, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.74/6.73  tff(c_205, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_185])).
% 13.74/6.73  tff(c_306, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.74/6.73  tff(c_321, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_205, c_306])).
% 13.74/6.73  tff(c_326, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_89, c_321])).
% 13.74/6.73  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.74/6.73  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.74/6.73  tff(c_48, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.74/6.73  tff(c_42, plain, (![B_34, A_33]: (k10_relat_1(k2_funct_1(B_34), A_33)=k9_relat_1(B_34, A_33) | ~v2_funct_1(B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.74/6.73  tff(c_32, plain, (![A_25]: (v1_funct_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.74/6.73  tff(c_34, plain, (![A_25]: (v1_relat_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.74/6.73  tff(c_30, plain, (![A_24]: (k10_relat_1(A_24, k2_relat_1(A_24))=k1_relat_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.74/6.73  tff(c_580, plain, (![B_85, A_86]: (k9_relat_1(k2_funct_1(B_85), A_86)=k10_relat_1(B_85, A_86) | ~v2_funct_1(B_85) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.74/6.73  tff(c_28, plain, (![B_23, A_22]: (r1_tarski(k9_relat_1(B_23, A_22), k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.74/6.73  tff(c_7464, plain, (![B_291, A_292]: (r1_tarski(k10_relat_1(B_291, A_292), k2_relat_1(k2_funct_1(B_291))) | ~v1_relat_1(k2_funct_1(B_291)) | ~v2_funct_1(B_291) | ~v1_funct_1(B_291) | ~v1_relat_1(B_291))), inference(superposition, [status(thm), theory('equality')], [c_580, c_28])).
% 13.74/6.73  tff(c_33316, plain, (![A_659]: (r1_tarski(k1_relat_1(A_659), k2_relat_1(k2_funct_1(A_659))) | ~v1_relat_1(k2_funct_1(A_659)) | ~v2_funct_1(A_659) | ~v1_funct_1(A_659) | ~v1_relat_1(A_659) | ~v1_relat_1(A_659))), inference(superposition, [status(thm), theory('equality')], [c_30, c_7464])).
% 13.74/6.73  tff(c_50, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.74/6.73  tff(c_118, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.74/6.73  tff(c_137, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_118])).
% 13.74/6.73  tff(c_353, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(k2_xboole_0(A_71, B_73), C_72))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.74/6.73  tff(c_360, plain, (![C_72]: (r1_tarski('#skF_1', C_72) | ~r1_tarski(k1_relat_1('#skF_3'), C_72))), inference(superposition, [status(thm), theory('equality')], [c_137, c_353])).
% 13.74/6.73  tff(c_33345, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_33316, c_360])).
% 13.74/6.73  tff(c_33378, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_48, c_33345])).
% 13.74/6.73  tff(c_33383, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_33378])).
% 13.74/6.73  tff(c_33386, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_33383])).
% 13.74/6.73  tff(c_33390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_33386])).
% 13.74/6.73  tff(c_33392, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_33378])).
% 13.74/6.73  tff(c_33391, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_33378])).
% 13.74/6.73  tff(c_38, plain, (![B_30, A_29]: (k9_relat_1(B_30, k10_relat_1(B_30, A_29))=A_29 | ~r1_tarski(A_29, k2_relat_1(B_30)) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.74/6.73  tff(c_33610, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_33391, c_38])).
% 13.74/6.73  tff(c_33628, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_33392, c_33610])).
% 13.74/6.73  tff(c_41886, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_33628])).
% 13.74/6.73  tff(c_41889, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_41886])).
% 13.74/6.73  tff(c_41893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_41889])).
% 13.74/6.73  tff(c_41894, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))='#skF_1'), inference(splitRight, [status(thm)], [c_33628])).
% 13.74/6.73  tff(c_44, plain, (![B_36, A_35]: (k9_relat_1(k2_funct_1(B_36), A_35)=k10_relat_1(B_36, A_35) | ~v2_funct_1(B_36) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.74/6.73  tff(c_41995, plain, (k10_relat_1('#skF_3', k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_41894, c_44])).
% 13.74/6.73  tff(c_42076, plain, (k10_relat_1('#skF_3', k10_relat_1(k2_funct_1('#skF_3'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_48, c_41995])).
% 13.74/6.73  tff(c_42109, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_42076])).
% 13.74/6.73  tff(c_42125, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_48, c_42109])).
% 13.74/6.73  tff(c_1791, plain, (![C_139, A_140, B_141]: (k3_xboole_0(k9_relat_1(C_139, A_140), k9_relat_1(C_139, B_141))=k9_relat_1(C_139, k3_xboole_0(A_140, B_141)) | ~v2_funct_1(C_139) | ~v1_funct_1(C_139) | ~v1_relat_1(C_139))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.74/6.73  tff(c_52, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.74/6.73  tff(c_201, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_185])).
% 13.74/6.73  tff(c_1822, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1791, c_201])).
% 13.74/6.73  tff(c_1859, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_48, c_1822])).
% 13.74/6.73  tff(c_40, plain, (![B_32, A_31]: (r1_tarski(k10_relat_1(B_32, k9_relat_1(B_32, A_31)), A_31) | ~v2_funct_1(B_32) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.74/6.73  tff(c_1874, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1859, c_40])).
% 13.74/6.73  tff(c_1885, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_48, c_1874])).
% 13.74/6.73  tff(c_42148, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42125, c_1885])).
% 13.74/6.73  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.74/6.73  tff(c_379, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.74/6.73  tff(c_398, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, k3_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_18, c_379])).
% 13.74/6.73  tff(c_42325, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_42148, c_398])).
% 13.74/6.73  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.74/6.73  tff(c_42599, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42325, c_12])).
% 13.74/6.73  tff(c_42682, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_326, c_42599])).
% 13.74/6.73  tff(c_42684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_42682])).
% 13.74/6.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.74/6.73  
% 13.74/6.73  Inference rules
% 13.74/6.73  ----------------------
% 13.74/6.73  #Ref     : 0
% 13.74/6.73  #Sup     : 10449
% 13.74/6.73  #Fact    : 0
% 13.74/6.73  #Define  : 0
% 13.74/6.73  #Split   : 9
% 13.74/6.73  #Chain   : 0
% 13.74/6.73  #Close   : 0
% 13.74/6.73  
% 13.74/6.73  Ordering : KBO
% 13.74/6.73  
% 13.74/6.73  Simplification rules
% 13.74/6.73  ----------------------
% 13.74/6.73  #Subsume      : 2151
% 13.74/6.73  #Demod        : 5511
% 13.74/6.73  #Tautology    : 4658
% 13.74/6.73  #SimpNegUnit  : 1
% 13.74/6.73  #BackRed      : 21
% 13.74/6.73  
% 13.74/6.73  #Partial instantiations: 0
% 13.74/6.73  #Strategies tried      : 1
% 13.74/6.73  
% 13.74/6.73  Timing (in seconds)
% 13.74/6.73  ----------------------
% 13.74/6.73  Preprocessing        : 0.31
% 13.74/6.73  Parsing              : 0.17
% 13.74/6.73  CNF conversion       : 0.02
% 13.74/6.73  Main loop            : 5.59
% 13.74/6.73  Inferencing          : 1.02
% 13.74/6.73  Reduction            : 2.74
% 13.74/6.73  Demodulation         : 2.30
% 13.74/6.73  BG Simplification    : 0.11
% 13.74/6.73  Subsumption          : 1.42
% 13.74/6.73  Abstraction          : 0.16
% 13.74/6.73  MUC search           : 0.00
% 13.74/6.73  Cooper               : 0.00
% 13.74/6.73  Total                : 5.93
% 13.74/6.73  Index Insertion      : 0.00
% 13.74/6.73  Index Deletion       : 0.00
% 13.74/6.73  Index Matching       : 0.00
% 13.74/6.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
