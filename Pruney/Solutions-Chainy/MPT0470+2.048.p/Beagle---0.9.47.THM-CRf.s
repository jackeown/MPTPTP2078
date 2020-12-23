%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:07 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 204 expanded)
%              Number of leaves         :   44 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  207 ( 391 expanded)
%              Number of equality atoms :   51 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_4 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_2 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_140,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_143,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_132,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_56,plain,
    ( k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_80,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    ! [A_38] :
      ( v1_relat_1(k4_relat_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_52] :
      ( v1_relat_1(A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_44,plain,(
    ! [A_42] :
      ( k4_relat_1(k4_relat_1(A_42)) = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | r2_hidden(k4_tarski('#skF_9'(A_49),'#skF_10'(A_49)),A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_736,plain,(
    ! [C_124,D_125,A_126] :
      ( r2_hidden(k4_tarski(C_124,D_125),k4_relat_1(A_126))
      | ~ r2_hidden(k4_tarski(D_125,C_124),A_126)
      | ~ v1_relat_1(k4_relat_1(A_126))
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1573,plain,(
    ! [A_168,D_169,C_170] :
      ( ~ v1_xboole_0(k4_relat_1(A_168))
      | ~ r2_hidden(k4_tarski(D_169,C_170),A_168)
      | ~ v1_relat_1(k4_relat_1(A_168))
      | ~ v1_relat_1(A_168) ) ),
    inference(resolution,[status(thm)],[c_736,c_2])).

tff(c_1598,plain,(
    ! [A_171] :
      ( ~ v1_xboole_0(k4_relat_1(A_171))
      | ~ v1_relat_1(k4_relat_1(A_171))
      | k1_xboole_0 = A_171
      | ~ v1_relat_1(A_171) ) ),
    inference(resolution,[status(thm)],[c_50,c_1573])).

tff(c_1602,plain,(
    ! [A_172] :
      ( ~ v1_xboole_0(A_172)
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(A_172)))
      | k4_relat_1(A_172) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_172))
      | ~ v1_relat_1(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1598])).

tff(c_1613,plain,(
    ! [A_173] :
      ( ~ v1_xboole_0(A_173)
      | k4_relat_1(A_173) = k1_xboole_0
      | ~ v1_relat_1(A_173)
      | ~ v1_relat_1(k4_relat_1(A_173)) ) ),
    inference(resolution,[status(thm)],[c_38,c_1602])).

tff(c_1621,plain,(
    ! [A_174] :
      ( ~ v1_xboole_0(A_174)
      | k4_relat_1(A_174) = k1_xboole_0
      | ~ v1_relat_1(A_174) ) ),
    inference(resolution,[status(thm)],[c_38,c_1613])).

tff(c_1630,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_1621])).

tff(c_1635,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1630])).

tff(c_40,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k5_relat_1(A_39,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_118,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),B_64)
      | r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    ! [B_64,A_63] :
      ( ~ v1_xboole_0(B_64)
      | r1_xboole_0(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_20,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_4'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_124,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_151,plain,(
    ! [A_74,B_75] :
      ( ~ r1_xboole_0(A_74,B_75)
      | k3_xboole_0(A_74,B_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_124])).

tff(c_174,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = k1_xboole_0
      | ~ v1_xboole_0(B_80) ) ),
    inference(resolution,[status(thm)],[c_122,c_151])).

tff(c_177,plain,(
    ! [A_79] : k3_xboole_0(A_79,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_174])).

tff(c_52,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_354,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_104,B_105)),k2_relat_1(B_105))
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_360,plain,(
    ! [A_104] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_104,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_354])).

tff(c_364,plain,(
    ! [A_106] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_106,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_360])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_367,plain,(
    ! [A_106] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_106,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_106,k1_xboole_0))
      | ~ v1_relat_1(A_106) ) ),
    inference(resolution,[status(thm)],[c_364,c_22])).

tff(c_370,plain,(
    ! [A_107] :
      ( k2_relat_1(k5_relat_1(A_107,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_367])).

tff(c_42,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k2_relat_1(A_41))
      | ~ v1_relat_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_385,plain,(
    ! [A_107] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_107,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_107,k1_xboole_0))
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_42])).

tff(c_591,plain,(
    ! [A_117] :
      ( ~ v1_relat_1(k5_relat_1(A_117,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_117,k1_xboole_0))
      | ~ v1_relat_1(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_385])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_606,plain,(
    ! [A_118] :
      ( k5_relat_1(A_118,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_118,k1_xboole_0))
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_591,c_8])).

tff(c_610,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_40,c_606])).

tff(c_614,plain,(
    ! [A_119] :
      ( k5_relat_1(A_119,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_610])).

tff(c_632,plain,(
    ! [A_38] :
      ( k5_relat_1(k4_relat_1(A_38),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_614])).

tff(c_570,plain,(
    ! [B_115,A_116] :
      ( k5_relat_1(k4_relat_1(B_115),k4_relat_1(A_116)) = k4_relat_1(k5_relat_1(A_116,B_115))
      | ~ v1_relat_1(B_115)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2922,plain,(
    ! [A_202,B_203] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_202),B_203)) = k5_relat_1(k4_relat_1(B_203),A_202)
      | ~ v1_relat_1(B_203)
      | ~ v1_relat_1(k4_relat_1(A_202))
      | ~ v1_relat_1(A_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_570])).

tff(c_3016,plain,(
    ! [A_38] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_38) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_38))
      | ~ v1_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_2922])).

tff(c_3041,plain,(
    ! [A_204] :
      ( k5_relat_1(k1_xboole_0,A_204) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_204))
      | ~ v1_relat_1(A_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1635,c_1635,c_3016])).

tff(c_3092,plain,(
    ! [A_205] :
      ( k5_relat_1(k1_xboole_0,A_205) = k1_xboole_0
      | ~ v1_relat_1(A_205) ) ),
    inference(resolution,[status(thm)],[c_38,c_3041])).

tff(c_3119,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_3092])).

tff(c_3132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3119])).

tff(c_3133,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3176,plain,(
    ! [A_212,B_213] :
      ( r2_hidden('#skF_2'(A_212,B_213),B_213)
      | r1_xboole_0(A_212,B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3180,plain,(
    ! [B_213,A_212] :
      ( ~ v1_xboole_0(B_213)
      | r1_xboole_0(A_212,B_213) ) ),
    inference(resolution,[status(thm)],[c_3176,c_2])).

tff(c_3188,plain,(
    ! [A_220,B_221,C_222] :
      ( ~ r1_xboole_0(A_220,B_221)
      | ~ r2_hidden(C_222,k3_xboole_0(A_220,B_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3218,plain,(
    ! [A_225,B_226] :
      ( ~ r1_xboole_0(A_225,B_226)
      | k3_xboole_0(A_225,B_226) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_3188])).

tff(c_3248,plain,(
    ! [A_230,B_231] :
      ( k3_xboole_0(A_230,B_231) = k1_xboole_0
      | ~ v1_xboole_0(B_231) ) ),
    inference(resolution,[status(thm)],[c_3180,c_3218])).

tff(c_3254,plain,(
    ! [A_230] : k3_xboole_0(A_230,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_3248])).

tff(c_3575,plain,(
    ! [A_260,B_261] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_260,B_261)),k2_relat_1(B_261))
      | ~ v1_relat_1(B_261)
      | ~ v1_relat_1(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3584,plain,(
    ! [A_260] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_260,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_3575])).

tff(c_3616,plain,(
    ! [A_264] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_264,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_3584])).

tff(c_3619,plain,(
    ! [A_264] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_264,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_264,k1_xboole_0))
      | ~ v1_relat_1(A_264) ) ),
    inference(resolution,[status(thm)],[c_3616,c_22])).

tff(c_3622,plain,(
    ! [A_265] :
      ( k2_relat_1(k5_relat_1(A_265,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_3619])).

tff(c_3637,plain,(
    ! [A_265] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_265,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_265,k1_xboole_0))
      | ~ v1_relat_1(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3622,c_42])).

tff(c_3671,plain,(
    ! [A_269] :
      ( ~ v1_relat_1(k5_relat_1(A_269,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_269,k1_xboole_0))
      | ~ v1_relat_1(A_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3637])).

tff(c_3698,plain,(
    ! [A_273] :
      ( k5_relat_1(A_273,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_273,k1_xboole_0))
      | ~ v1_relat_1(A_273) ) ),
    inference(resolution,[status(thm)],[c_3671,c_8])).

tff(c_3702,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_40,c_3698])).

tff(c_3706,plain,(
    ! [A_274] :
      ( k5_relat_1(A_274,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_3702])).

tff(c_3721,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_3706])).

tff(c_3729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3133,c_3721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.84  
% 4.70/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_4 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_2 > #skF_7 > #skF_5
% 4.70/1.84  
% 4.70/1.84  %Foreground sorts:
% 4.70/1.84  
% 4.70/1.84  
% 4.70/1.84  %Background operators:
% 4.70/1.84  
% 4.70/1.84  
% 4.70/1.84  %Foreground operators:
% 4.70/1.84  tff('#skF_9', type, '#skF_9': $i > $i).
% 4.70/1.84  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.70/1.84  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.70/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/1.84  tff('#skF_11', type, '#skF_11': $i).
% 4.70/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.70/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.70/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.70/1.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.70/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.70/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.70/1.84  tff('#skF_10', type, '#skF_10': $i > $i).
% 4.70/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.70/1.84  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.70/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.70/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.70/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.70/1.84  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.70/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/1.84  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.70/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.70/1.84  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.70/1.84  
% 4.78/1.86  tff(f_150, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 4.78/1.86  tff(f_100, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.78/1.86  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.78/1.86  tff(f_84, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.78/1.86  tff(f_118, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 4.78/1.86  tff(f_140, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 4.78/1.86  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 4.78/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.78/1.86  tff(f_106, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.78/1.86  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.78/1.86  tff(f_76, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.78/1.86  tff(f_68, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.78/1.86  tff(f_143, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.78/1.86  tff(f_125, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 4.78/1.86  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.78/1.86  tff(f_114, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 4.78/1.86  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.78/1.86  tff(f_132, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 4.78/1.86  tff(c_56, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.78/1.86  tff(c_80, plain, (k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 4.78/1.86  tff(c_58, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.78/1.86  tff(c_38, plain, (![A_38]: (v1_relat_1(k4_relat_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.78/1.86  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.78/1.86  tff(c_67, plain, (![A_52]: (v1_relat_1(A_52) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.78/1.86  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_67])).
% 4.78/1.86  tff(c_44, plain, (![A_42]: (k4_relat_1(k4_relat_1(A_42))=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.78/1.86  tff(c_50, plain, (![A_49]: (k1_xboole_0=A_49 | r2_hidden(k4_tarski('#skF_9'(A_49), '#skF_10'(A_49)), A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.78/1.86  tff(c_736, plain, (![C_124, D_125, A_126]: (r2_hidden(k4_tarski(C_124, D_125), k4_relat_1(A_126)) | ~r2_hidden(k4_tarski(D_125, C_124), A_126) | ~v1_relat_1(k4_relat_1(A_126)) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.78/1.86  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.78/1.86  tff(c_1573, plain, (![A_168, D_169, C_170]: (~v1_xboole_0(k4_relat_1(A_168)) | ~r2_hidden(k4_tarski(D_169, C_170), A_168) | ~v1_relat_1(k4_relat_1(A_168)) | ~v1_relat_1(A_168))), inference(resolution, [status(thm)], [c_736, c_2])).
% 4.78/1.86  tff(c_1598, plain, (![A_171]: (~v1_xboole_0(k4_relat_1(A_171)) | ~v1_relat_1(k4_relat_1(A_171)) | k1_xboole_0=A_171 | ~v1_relat_1(A_171))), inference(resolution, [status(thm)], [c_50, c_1573])).
% 4.78/1.86  tff(c_1602, plain, (![A_172]: (~v1_xboole_0(A_172) | ~v1_relat_1(k4_relat_1(k4_relat_1(A_172))) | k4_relat_1(A_172)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_172)) | ~v1_relat_1(A_172))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1598])).
% 4.78/1.86  tff(c_1613, plain, (![A_173]: (~v1_xboole_0(A_173) | k4_relat_1(A_173)=k1_xboole_0 | ~v1_relat_1(A_173) | ~v1_relat_1(k4_relat_1(A_173)))), inference(resolution, [status(thm)], [c_38, c_1602])).
% 4.78/1.86  tff(c_1621, plain, (![A_174]: (~v1_xboole_0(A_174) | k4_relat_1(A_174)=k1_xboole_0 | ~v1_relat_1(A_174))), inference(resolution, [status(thm)], [c_38, c_1613])).
% 4.78/1.86  tff(c_1630, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1621])).
% 4.78/1.86  tff(c_1635, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1630])).
% 4.78/1.86  tff(c_40, plain, (![A_39, B_40]: (v1_relat_1(k5_relat_1(A_39, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.78/1.86  tff(c_118, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), B_64) | r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.78/1.86  tff(c_122, plain, (![B_64, A_63]: (~v1_xboole_0(B_64) | r1_xboole_0(A_63, B_64))), inference(resolution, [status(thm)], [c_118, c_2])).
% 4.78/1.86  tff(c_20, plain, (![A_16]: (r2_hidden('#skF_4'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.78/1.86  tff(c_124, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.78/1.86  tff(c_151, plain, (![A_74, B_75]: (~r1_xboole_0(A_74, B_75) | k3_xboole_0(A_74, B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_124])).
% 4.78/1.86  tff(c_174, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=k1_xboole_0 | ~v1_xboole_0(B_80))), inference(resolution, [status(thm)], [c_122, c_151])).
% 4.78/1.86  tff(c_177, plain, (![A_79]: (k3_xboole_0(A_79, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_174])).
% 4.78/1.86  tff(c_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.78/1.86  tff(c_354, plain, (![A_104, B_105]: (r1_tarski(k2_relat_1(k5_relat_1(A_104, B_105)), k2_relat_1(B_105)) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.78/1.86  tff(c_360, plain, (![A_104]: (r1_tarski(k2_relat_1(k5_relat_1(A_104, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_52, c_354])).
% 4.78/1.86  tff(c_364, plain, (![A_106]: (r1_tarski(k2_relat_1(k5_relat_1(A_106, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_360])).
% 4.78/1.86  tff(c_22, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.78/1.86  tff(c_367, plain, (![A_106]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_106, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_106, k1_xboole_0)) | ~v1_relat_1(A_106))), inference(resolution, [status(thm)], [c_364, c_22])).
% 4.78/1.86  tff(c_370, plain, (![A_107]: (k2_relat_1(k5_relat_1(A_107, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_367])).
% 4.78/1.86  tff(c_42, plain, (![A_41]: (~v1_xboole_0(k2_relat_1(A_41)) | ~v1_relat_1(A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.78/1.86  tff(c_385, plain, (![A_107]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_107, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_107, k1_xboole_0)) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_370, c_42])).
% 4.78/1.86  tff(c_591, plain, (![A_117]: (~v1_relat_1(k5_relat_1(A_117, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_117, k1_xboole_0)) | ~v1_relat_1(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_385])).
% 4.78/1.86  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.78/1.86  tff(c_606, plain, (![A_118]: (k5_relat_1(A_118, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_118, k1_xboole_0)) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_591, c_8])).
% 4.78/1.86  tff(c_610, plain, (![A_39]: (k5_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_40, c_606])).
% 4.78/1.86  tff(c_614, plain, (![A_119]: (k5_relat_1(A_119, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_610])).
% 4.78/1.86  tff(c_632, plain, (![A_38]: (k5_relat_1(k4_relat_1(A_38), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_38, c_614])).
% 4.78/1.86  tff(c_570, plain, (![B_115, A_116]: (k5_relat_1(k4_relat_1(B_115), k4_relat_1(A_116))=k4_relat_1(k5_relat_1(A_116, B_115)) | ~v1_relat_1(B_115) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.78/1.86  tff(c_2922, plain, (![A_202, B_203]: (k4_relat_1(k5_relat_1(k4_relat_1(A_202), B_203))=k5_relat_1(k4_relat_1(B_203), A_202) | ~v1_relat_1(B_203) | ~v1_relat_1(k4_relat_1(A_202)) | ~v1_relat_1(A_202))), inference(superposition, [status(thm), theory('equality')], [c_44, c_570])).
% 4.78/1.86  tff(c_3016, plain, (![A_38]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_38)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_38)) | ~v1_relat_1(A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_632, c_2922])).
% 4.78/1.86  tff(c_3041, plain, (![A_204]: (k5_relat_1(k1_xboole_0, A_204)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_204)) | ~v1_relat_1(A_204))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1635, c_1635, c_3016])).
% 4.78/1.86  tff(c_3092, plain, (![A_205]: (k5_relat_1(k1_xboole_0, A_205)=k1_xboole_0 | ~v1_relat_1(A_205))), inference(resolution, [status(thm)], [c_38, c_3041])).
% 4.78/1.86  tff(c_3119, plain, (k5_relat_1(k1_xboole_0, '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_3092])).
% 4.78/1.86  tff(c_3132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_3119])).
% 4.78/1.86  tff(c_3133, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 4.78/1.86  tff(c_3176, plain, (![A_212, B_213]: (r2_hidden('#skF_2'(A_212, B_213), B_213) | r1_xboole_0(A_212, B_213))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.78/1.86  tff(c_3180, plain, (![B_213, A_212]: (~v1_xboole_0(B_213) | r1_xboole_0(A_212, B_213))), inference(resolution, [status(thm)], [c_3176, c_2])).
% 4.78/1.86  tff(c_3188, plain, (![A_220, B_221, C_222]: (~r1_xboole_0(A_220, B_221) | ~r2_hidden(C_222, k3_xboole_0(A_220, B_221)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.78/1.86  tff(c_3218, plain, (![A_225, B_226]: (~r1_xboole_0(A_225, B_226) | k3_xboole_0(A_225, B_226)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_3188])).
% 4.78/1.86  tff(c_3248, plain, (![A_230, B_231]: (k3_xboole_0(A_230, B_231)=k1_xboole_0 | ~v1_xboole_0(B_231))), inference(resolution, [status(thm)], [c_3180, c_3218])).
% 4.78/1.86  tff(c_3254, plain, (![A_230]: (k3_xboole_0(A_230, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_3248])).
% 4.78/1.86  tff(c_3575, plain, (![A_260, B_261]: (r1_tarski(k2_relat_1(k5_relat_1(A_260, B_261)), k2_relat_1(B_261)) | ~v1_relat_1(B_261) | ~v1_relat_1(A_260))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.78/1.86  tff(c_3584, plain, (![A_260]: (r1_tarski(k2_relat_1(k5_relat_1(A_260, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_260))), inference(superposition, [status(thm), theory('equality')], [c_52, c_3575])).
% 4.78/1.86  tff(c_3616, plain, (![A_264]: (r1_tarski(k2_relat_1(k5_relat_1(A_264, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_264))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_3584])).
% 4.78/1.86  tff(c_3619, plain, (![A_264]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_264, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_264, k1_xboole_0)) | ~v1_relat_1(A_264))), inference(resolution, [status(thm)], [c_3616, c_22])).
% 4.78/1.86  tff(c_3622, plain, (![A_265]: (k2_relat_1(k5_relat_1(A_265, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_265))), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_3619])).
% 4.78/1.86  tff(c_3637, plain, (![A_265]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_265, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_265, k1_xboole_0)) | ~v1_relat_1(A_265))), inference(superposition, [status(thm), theory('equality')], [c_3622, c_42])).
% 4.78/1.86  tff(c_3671, plain, (![A_269]: (~v1_relat_1(k5_relat_1(A_269, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_269, k1_xboole_0)) | ~v1_relat_1(A_269))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3637])).
% 4.78/1.86  tff(c_3698, plain, (![A_273]: (k5_relat_1(A_273, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_273, k1_xboole_0)) | ~v1_relat_1(A_273))), inference(resolution, [status(thm)], [c_3671, c_8])).
% 4.78/1.86  tff(c_3702, plain, (![A_39]: (k5_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_40, c_3698])).
% 4.78/1.86  tff(c_3706, plain, (![A_274]: (k5_relat_1(A_274, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_274))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_3702])).
% 4.78/1.86  tff(c_3721, plain, (k5_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_3706])).
% 4.78/1.86  tff(c_3729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3133, c_3721])).
% 4.78/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.86  
% 4.78/1.86  Inference rules
% 4.78/1.86  ----------------------
% 4.78/1.86  #Ref     : 0
% 4.78/1.86  #Sup     : 863
% 4.78/1.86  #Fact    : 0
% 4.78/1.86  #Define  : 0
% 4.78/1.86  #Split   : 5
% 4.78/1.86  #Chain   : 0
% 4.78/1.86  #Close   : 0
% 4.78/1.86  
% 4.78/1.86  Ordering : KBO
% 4.78/1.86  
% 4.78/1.86  Simplification rules
% 4.78/1.86  ----------------------
% 4.78/1.86  #Subsume      : 186
% 4.78/1.86  #Demod        : 732
% 4.78/1.86  #Tautology    : 415
% 4.78/1.86  #SimpNegUnit  : 31
% 4.78/1.86  #BackRed      : 8
% 4.78/1.86  
% 4.78/1.86  #Partial instantiations: 0
% 4.78/1.86  #Strategies tried      : 1
% 4.78/1.86  
% 4.78/1.86  Timing (in seconds)
% 4.78/1.86  ----------------------
% 4.78/1.86  Preprocessing        : 0.32
% 4.78/1.86  Parsing              : 0.18
% 4.78/1.86  CNF conversion       : 0.03
% 4.78/1.86  Main loop            : 0.76
% 4.78/1.86  Inferencing          : 0.27
% 4.78/1.86  Reduction            : 0.23
% 4.78/1.86  Demodulation         : 0.16
% 4.78/1.86  BG Simplification    : 0.03
% 4.78/1.86  Subsumption          : 0.17
% 4.78/1.86  Abstraction          : 0.03
% 4.78/1.86  MUC search           : 0.00
% 4.78/1.86  Cooper               : 0.00
% 4.78/1.86  Total                : 1.12
% 4.78/1.86  Index Insertion      : 0.00
% 4.78/1.86  Index Deletion       : 0.00
% 4.78/1.86  Index Matching       : 0.00
% 4.78/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
