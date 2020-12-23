%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:27 EST 2020

% Result     : Theorem 39.60s
% Output     : CNFRefutation 39.67s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 168 expanded)
%              Number of leaves         :   37 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :  173 ( 390 expanded)
%              Number of equality atoms :   36 (  72 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_130,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
          & r1_tarski(A,k1_relat_1(C))
          & v2_funct_1(C) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_50,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_58,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_12,c_84])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k10_relat_1(B_15,A_14),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_581,plain,(
    ! [B_92,A_93] :
      ( k9_relat_1(B_92,k10_relat_1(B_92,A_93)) = A_93
      | ~ r1_tarski(A_93,k2_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_600,plain,(
    ! [B_92] :
      ( k9_relat_1(B_92,k10_relat_1(B_92,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_12,c_581])).

tff(c_14,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_318,plain,(
    ! [B_79,A_80] :
      ( k9_relat_1(B_79,A_80) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_79),A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_338,plain,(
    ! [B_81] :
      ( k9_relat_1(B_81,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_14,c_318])).

tff(c_346,plain,(
    k9_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_338])).

tff(c_1257,plain,(
    ! [A_128,B_129,C_130] :
      ( r1_tarski(A_128,B_129)
      | ~ v2_funct_1(C_130)
      | ~ r1_tarski(A_128,k1_relat_1(C_130))
      | ~ r1_tarski(k9_relat_1(C_130,A_128),k9_relat_1(C_130,B_129))
      | ~ v1_funct_1(C_130)
      | ~ v1_relat_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1281,plain,(
    ! [A_128] :
      ( r1_tarski(A_128,k1_xboole_0)
      | ~ v2_funct_1('#skF_2')
      | ~ r1_tarski(A_128,k1_relat_1('#skF_2'))
      | ~ r1_tarski(k9_relat_1('#skF_2',A_128),k1_xboole_0)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_1257])).

tff(c_1835,plain,(
    ! [A_148] :
      ( r1_tarski(A_148,k1_xboole_0)
      | ~ r1_tarski(A_148,k1_relat_1('#skF_2'))
      | ~ r1_tarski(k9_relat_1('#skF_2',A_148),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_1281])).

tff(c_1839,plain,
    ( r1_tarski(k10_relat_1('#skF_2',k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k10_relat_1('#skF_2',k1_xboole_0),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_1835])).

tff(c_1848,plain,
    ( r1_tarski(k10_relat_1('#skF_2',k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k10_relat_1('#skF_2',k1_xboole_0),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_6,c_1839])).

tff(c_2230,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k1_xboole_0),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1848])).

tff(c_2233,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2230])).

tff(c_2237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2233])).

tff(c_2238,plain,(
    r1_tarski(k10_relat_1('#skF_2',k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1848])).

tff(c_198,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_198])).

tff(c_2248,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2238,c_215])).

tff(c_28,plain,(
    ! [A_19,B_21] :
      ( k10_relat_1(A_19,k1_relat_1(B_21)) = k1_relat_1(k5_relat_1(A_19,B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_817,plain,(
    ! [C_108,A_109,B_110] :
      ( k2_xboole_0(k10_relat_1(C_108,A_109),k10_relat_1(C_108,B_110)) = k10_relat_1(C_108,k2_xboole_0(A_109,B_110))
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5859,plain,(
    ! [A_263,A_264,B_265] :
      ( k2_xboole_0(k10_relat_1(A_263,A_264),k1_relat_1(k5_relat_1(A_263,B_265))) = k10_relat_1(A_263,k2_xboole_0(A_264,k1_relat_1(B_265)))
      | ~ v1_relat_1(A_263)
      | ~ v1_relat_1(B_265)
      | ~ v1_relat_1(A_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_817])).

tff(c_5945,plain,(
    ! [B_265] :
      ( k2_xboole_0(k1_xboole_0,k1_relat_1(k5_relat_1('#skF_2',B_265))) = k10_relat_1('#skF_2',k2_xboole_0(k1_xboole_0,k1_relat_1(B_265)))
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(B_265)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2248,c_5859])).

tff(c_59783,plain,(
    ! [B_805] :
      ( k10_relat_1('#skF_2',k1_relat_1(B_805)) = k1_relat_1(k5_relat_1('#skF_2',B_805))
      | ~ v1_relat_1(B_805) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_99,c_99,c_5945])).

tff(c_59883,plain,(
    ! [A_22] :
      ( k1_relat_1(k5_relat_1('#skF_2',k6_relat_1(A_22))) = k10_relat_1('#skF_2',A_22)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_59783])).

tff(c_59941,plain,(
    ! [A_806] : k1_relat_1(k5_relat_1('#skF_2',k6_relat_1(A_806))) = k10_relat_1('#skF_2',A_806) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59883])).

tff(c_351,plain,(
    ! [A_82,B_83] :
      ( k10_relat_1(A_82,k1_relat_1(B_83)) = k1_relat_1(k5_relat_1(A_82,B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_369,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_82,B_83)),k1_relat_1(A_82))
      | ~ v1_relat_1(A_82)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_24])).

tff(c_60021,plain,(
    ! [A_806] :
      ( r1_tarski(k10_relat_1('#skF_2',A_806),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k6_relat_1(A_806))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59941,c_369])).

tff(c_60213,plain,(
    ! [A_810] : r1_tarski(k10_relat_1('#skF_2',A_810),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34,c_58,c_60021])).

tff(c_1033,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,k9_relat_1(B_122,k1_relat_1(B_122))) = k9_relat_1(B_122,k10_relat_1(B_122,A_121))
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2108,plain,(
    ! [B_157,A_158] :
      ( r1_tarski(k9_relat_1(B_157,k10_relat_1(B_157,A_158)),A_158)
      | ~ v1_funct_1(B_157)
      | ~ v1_relat_1(B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_10])).

tff(c_46,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_tarski(A_35,B_36)
      | ~ v2_funct_1(C_37)
      | ~ r1_tarski(A_35,k1_relat_1(C_37))
      | ~ r1_tarski(k9_relat_1(C_37,A_35),k9_relat_1(C_37,B_36))
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2157,plain,(
    ! [B_157,B_36] :
      ( r1_tarski(k10_relat_1(B_157,k9_relat_1(B_157,B_36)),B_36)
      | ~ v2_funct_1(B_157)
      | ~ r1_tarski(k10_relat_1(B_157,k9_relat_1(B_157,B_36)),k1_relat_1(B_157))
      | ~ v1_funct_1(B_157)
      | ~ v1_relat_1(B_157) ) ),
    inference(resolution,[status(thm)],[c_2108,c_46])).

tff(c_60219,plain,(
    ! [B_36] :
      ( r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_36)),B_36)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60213,c_2157])).

tff(c_60431,plain,(
    ! [B_812] : r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_812)),B_812) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_60219])).

tff(c_475,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(A_88,k10_relat_1(B_89,k9_relat_1(B_89,A_88)))
      | ~ r1_tarski(A_88,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_500,plain,(
    ! [B_89,A_88] :
      ( k10_relat_1(B_89,k9_relat_1(B_89,A_88)) = A_88
      | ~ r1_tarski(k10_relat_1(B_89,k9_relat_1(B_89,A_88)),A_88)
      | ~ r1_tarski(A_88,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_475,c_2])).

tff(c_60455,plain,(
    ! [B_812] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_812)) = B_812
      | ~ r1_tarski(B_812,k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60431,c_500])).

tff(c_165055,plain,(
    ! [B_1358] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1358)) = B_1358
      | ~ r1_tarski(B_1358,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60455])).

tff(c_165306,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_165055])).

tff(c_165395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_165306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.60/30.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.60/30.87  
% 39.60/30.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.60/30.87  %$ r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 39.60/30.87  
% 39.60/30.87  %Foreground sorts:
% 39.60/30.87  
% 39.60/30.87  
% 39.60/30.87  %Background operators:
% 39.60/30.87  
% 39.60/30.87  
% 39.60/30.87  %Foreground operators:
% 39.60/30.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 39.60/30.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 39.60/30.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.60/30.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 39.60/30.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 39.60/30.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.60/30.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 39.60/30.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 39.60/30.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 39.60/30.87  tff('#skF_2', type, '#skF_2': $i).
% 39.60/30.87  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 39.60/30.87  tff('#skF_1', type, '#skF_1': $i).
% 39.60/30.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.60/30.87  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 39.60/30.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 39.60/30.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 39.60/30.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.60/30.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 39.60/30.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.60/30.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 39.60/30.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 39.60/30.87  
% 39.67/30.89  tff(f_130, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 39.67/30.89  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 39.67/30.89  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 39.67/30.89  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 39.67/30.89  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 39.67/30.89  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 39.67/30.89  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 39.67/30.89  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 39.67/30.89  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 39.67/30.89  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 39.67/30.89  tff(f_117, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 39.67/30.89  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 39.67/30.89  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 39.67/30.89  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 39.67/30.89  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 39.67/30.89  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 39.67/30.89  tff(c_50, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_130])).
% 39.67/30.89  tff(c_54, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 39.67/30.89  tff(c_58, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 39.67/30.89  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 39.67/30.89  tff(c_52, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 39.67/30.89  tff(c_34, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 39.67/30.89  tff(c_30, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_72])).
% 39.67/30.89  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.67/30.89  tff(c_84, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 39.67/30.89  tff(c_99, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(resolution, [status(thm)], [c_12, c_84])).
% 39.67/30.89  tff(c_24, plain, (![B_15, A_14]: (r1_tarski(k10_relat_1(B_15, A_14), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 39.67/30.89  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.67/30.89  tff(c_581, plain, (![B_92, A_93]: (k9_relat_1(B_92, k10_relat_1(B_92, A_93))=A_93 | ~r1_tarski(A_93, k2_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_99])).
% 39.67/30.89  tff(c_600, plain, (![B_92]: (k9_relat_1(B_92, k10_relat_1(B_92, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_12, c_581])).
% 39.67/30.89  tff(c_14, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 39.67/30.89  tff(c_318, plain, (![B_79, A_80]: (k9_relat_1(B_79, A_80)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_79), A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_53])).
% 39.67/30.89  tff(c_338, plain, (![B_81]: (k9_relat_1(B_81, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_14, c_318])).
% 39.67/30.89  tff(c_346, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_338])).
% 39.67/30.89  tff(c_1257, plain, (![A_128, B_129, C_130]: (r1_tarski(A_128, B_129) | ~v2_funct_1(C_130) | ~r1_tarski(A_128, k1_relat_1(C_130)) | ~r1_tarski(k9_relat_1(C_130, A_128), k9_relat_1(C_130, B_129)) | ~v1_funct_1(C_130) | ~v1_relat_1(C_130))), inference(cnfTransformation, [status(thm)], [f_117])).
% 39.67/30.89  tff(c_1281, plain, (![A_128]: (r1_tarski(A_128, k1_xboole_0) | ~v2_funct_1('#skF_2') | ~r1_tarski(A_128, k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_2', A_128), k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_1257])).
% 39.67/30.89  tff(c_1835, plain, (![A_148]: (r1_tarski(A_148, k1_xboole_0) | ~r1_tarski(A_148, k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_2', A_148), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_1281])).
% 39.67/30.89  tff(c_1839, plain, (r1_tarski(k10_relat_1('#skF_2', k1_xboole_0), k1_xboole_0) | ~r1_tarski(k10_relat_1('#skF_2', k1_xboole_0), k1_relat_1('#skF_2')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_600, c_1835])).
% 39.67/30.89  tff(c_1848, plain, (r1_tarski(k10_relat_1('#skF_2', k1_xboole_0), k1_xboole_0) | ~r1_tarski(k10_relat_1('#skF_2', k1_xboole_0), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_6, c_1839])).
% 39.67/30.89  tff(c_2230, plain, (~r1_tarski(k10_relat_1('#skF_2', k1_xboole_0), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1848])).
% 39.67/30.89  tff(c_2233, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2230])).
% 39.67/30.89  tff(c_2237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_2233])).
% 39.67/30.89  tff(c_2238, plain, (r1_tarski(k10_relat_1('#skF_2', k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1848])).
% 39.67/30.89  tff(c_198, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.67/30.89  tff(c_215, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_198])).
% 39.67/30.89  tff(c_2248, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2238, c_215])).
% 39.67/30.89  tff(c_28, plain, (![A_19, B_21]: (k10_relat_1(A_19, k1_relat_1(B_21))=k1_relat_1(k5_relat_1(A_19, B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 39.67/30.89  tff(c_817, plain, (![C_108, A_109, B_110]: (k2_xboole_0(k10_relat_1(C_108, A_109), k10_relat_1(C_108, B_110))=k10_relat_1(C_108, k2_xboole_0(A_109, B_110)) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_61])).
% 39.67/30.89  tff(c_5859, plain, (![A_263, A_264, B_265]: (k2_xboole_0(k10_relat_1(A_263, A_264), k1_relat_1(k5_relat_1(A_263, B_265)))=k10_relat_1(A_263, k2_xboole_0(A_264, k1_relat_1(B_265))) | ~v1_relat_1(A_263) | ~v1_relat_1(B_265) | ~v1_relat_1(A_263))), inference(superposition, [status(thm), theory('equality')], [c_28, c_817])).
% 39.67/30.89  tff(c_5945, plain, (![B_265]: (k2_xboole_0(k1_xboole_0, k1_relat_1(k5_relat_1('#skF_2', B_265)))=k10_relat_1('#skF_2', k2_xboole_0(k1_xboole_0, k1_relat_1(B_265))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(B_265) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2248, c_5859])).
% 39.67/30.89  tff(c_59783, plain, (![B_805]: (k10_relat_1('#skF_2', k1_relat_1(B_805))=k1_relat_1(k5_relat_1('#skF_2', B_805)) | ~v1_relat_1(B_805))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_99, c_99, c_5945])).
% 39.67/30.89  tff(c_59883, plain, (![A_22]: (k1_relat_1(k5_relat_1('#skF_2', k6_relat_1(A_22)))=k10_relat_1('#skF_2', A_22) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_59783])).
% 39.67/30.89  tff(c_59941, plain, (![A_806]: (k1_relat_1(k5_relat_1('#skF_2', k6_relat_1(A_806)))=k10_relat_1('#skF_2', A_806))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59883])).
% 39.67/30.89  tff(c_351, plain, (![A_82, B_83]: (k10_relat_1(A_82, k1_relat_1(B_83))=k1_relat_1(k5_relat_1(A_82, B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_68])).
% 39.67/30.89  tff(c_369, plain, (![A_82, B_83]: (r1_tarski(k1_relat_1(k5_relat_1(A_82, B_83)), k1_relat_1(A_82)) | ~v1_relat_1(A_82) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_351, c_24])).
% 39.67/30.89  tff(c_60021, plain, (![A_806]: (r1_tarski(k10_relat_1('#skF_2', A_806), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1(A_806)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_59941, c_369])).
% 39.67/30.89  tff(c_60213, plain, (![A_810]: (r1_tarski(k10_relat_1('#skF_2', A_810), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34, c_58, c_60021])).
% 39.67/30.89  tff(c_1033, plain, (![A_121, B_122]: (k3_xboole_0(A_121, k9_relat_1(B_122, k1_relat_1(B_122)))=k9_relat_1(B_122, k10_relat_1(B_122, A_121)) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_105])).
% 39.67/30.89  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 39.67/30.89  tff(c_2108, plain, (![B_157, A_158]: (r1_tarski(k9_relat_1(B_157, k10_relat_1(B_157, A_158)), A_158) | ~v1_funct_1(B_157) | ~v1_relat_1(B_157))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_10])).
% 39.67/30.89  tff(c_46, plain, (![A_35, B_36, C_37]: (r1_tarski(A_35, B_36) | ~v2_funct_1(C_37) | ~r1_tarski(A_35, k1_relat_1(C_37)) | ~r1_tarski(k9_relat_1(C_37, A_35), k9_relat_1(C_37, B_36)) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_117])).
% 39.67/30.89  tff(c_2157, plain, (![B_157, B_36]: (r1_tarski(k10_relat_1(B_157, k9_relat_1(B_157, B_36)), B_36) | ~v2_funct_1(B_157) | ~r1_tarski(k10_relat_1(B_157, k9_relat_1(B_157, B_36)), k1_relat_1(B_157)) | ~v1_funct_1(B_157) | ~v1_relat_1(B_157))), inference(resolution, [status(thm)], [c_2108, c_46])).
% 39.67/30.89  tff(c_60219, plain, (![B_36]: (r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_36)), B_36) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_60213, c_2157])).
% 39.67/30.89  tff(c_60431, plain, (![B_812]: (r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_812)), B_812))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_60219])).
% 39.67/30.89  tff(c_475, plain, (![A_88, B_89]: (r1_tarski(A_88, k10_relat_1(B_89, k9_relat_1(B_89, A_88))) | ~r1_tarski(A_88, k1_relat_1(B_89)) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_91])).
% 39.67/30.89  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.67/30.89  tff(c_500, plain, (![B_89, A_88]: (k10_relat_1(B_89, k9_relat_1(B_89, A_88))=A_88 | ~r1_tarski(k10_relat_1(B_89, k9_relat_1(B_89, A_88)), A_88) | ~r1_tarski(A_88, k1_relat_1(B_89)) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_475, c_2])).
% 39.67/30.89  tff(c_60455, plain, (![B_812]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_812))=B_812 | ~r1_tarski(B_812, k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_60431, c_500])).
% 39.67/30.89  tff(c_165055, plain, (![B_1358]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1358))=B_1358 | ~r1_tarski(B_1358, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60455])).
% 39.67/30.89  tff(c_165306, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(resolution, [status(thm)], [c_54, c_165055])).
% 39.67/30.89  tff(c_165395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_165306])).
% 39.67/30.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.67/30.89  
% 39.67/30.89  Inference rules
% 39.67/30.89  ----------------------
% 39.67/30.89  #Ref     : 5
% 39.67/30.89  #Sup     : 41861
% 39.67/30.89  #Fact    : 0
% 39.67/30.89  #Define  : 0
% 39.67/30.89  #Split   : 21
% 39.67/30.89  #Chain   : 0
% 39.67/30.89  #Close   : 0
% 39.67/30.89  
% 39.67/30.89  Ordering : KBO
% 39.67/30.89  
% 39.67/30.89  Simplification rules
% 39.67/30.89  ----------------------
% 39.67/30.89  #Subsume      : 21234
% 39.67/30.89  #Demod        : 32276
% 39.67/30.89  #Tautology    : 11556
% 39.67/30.89  #SimpNegUnit  : 1360
% 39.67/30.89  #BackRed      : 147
% 39.67/30.89  
% 39.67/30.89  #Partial instantiations: 0
% 39.67/30.89  #Strategies tried      : 1
% 39.67/30.89  
% 39.67/30.89  Timing (in seconds)
% 39.67/30.89  ----------------------
% 39.67/30.89  Preprocessing        : 0.33
% 39.67/30.89  Parsing              : 0.18
% 39.67/30.89  CNF conversion       : 0.02
% 39.67/30.89  Main loop            : 29.79
% 39.67/30.89  Inferencing          : 2.97
% 39.67/30.89  Reduction            : 17.21
% 39.67/30.89  Demodulation         : 14.57
% 39.67/30.89  BG Simplification    : 0.25
% 39.67/30.89  Subsumption          : 8.53
% 39.67/30.89  Abstraction          : 0.51
% 39.67/30.89  MUC search           : 0.00
% 39.67/30.89  Cooper               : 0.00
% 39.67/30.89  Total                : 30.16
% 39.67/30.89  Index Insertion      : 0.00
% 39.67/30.89  Index Deletion       : 0.00
% 39.67/30.89  Index Matching       : 0.00
% 39.67/30.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
