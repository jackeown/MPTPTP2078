%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0720+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:45 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   55 (  66 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 160 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B)
              & v5_funct_1(B,A) )
           => r1_tarski(k1_relat_1(B),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    v5_funct_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),A_11)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_43,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_47,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_43])).

tff(c_48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_22])).

tff(c_115,plain,(
    ! [A_59,B_60] :
      ( k1_funct_1(A_59,B_60) = k1_xboole_0
      | r2_hidden(B_60,k1_relat_1(A_59))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12),B_12)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_126,plain,(
    ! [A_11,A_59] :
      ( r1_tarski(A_11,k1_relat_1(A_59))
      | k1_funct_1(A_59,'#skF_2'(A_11,k1_relat_1(A_59))) = k1_xboole_0
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_115,c_10])).

tff(c_65,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_2'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_35] : r1_tarski(A_35,A_35) ),
    inference(resolution,[status(thm)],[c_65,c_10])).

tff(c_266,plain,(
    ! [B_98,C_99,A_100] :
      ( r2_hidden(k1_funct_1(B_98,C_99),k1_funct_1(A_100,C_99))
      | ~ r2_hidden(C_99,k1_relat_1(B_98))
      | ~ v5_funct_1(B_98,A_100)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_75,plain,(
    ! [B_22,A_40,A_21] :
      ( ~ v1_xboole_0(B_22)
      | ~ r2_hidden(A_40,A_21)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_465,plain,(
    ! [B_138,A_139,C_140,B_141] :
      ( ~ v1_xboole_0(B_138)
      | ~ r1_tarski(k1_funct_1(A_139,C_140),B_138)
      | ~ r2_hidden(C_140,k1_relat_1(B_141))
      | ~ v5_funct_1(B_141,A_139)
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_266,c_75])).

tff(c_476,plain,(
    ! [A_142,C_143,B_144] :
      ( ~ v1_xboole_0(k1_funct_1(A_142,C_143))
      | ~ r2_hidden(C_143,k1_relat_1(B_144))
      | ~ v5_funct_1(B_144,A_142)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(A_142)
      | ~ v1_relat_1(A_142) ) ),
    inference(resolution,[status(thm)],[c_70,c_465])).

tff(c_478,plain,(
    ! [A_11,A_59,B_144] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_11,k1_relat_1(A_59)),k1_relat_1(B_144))
      | ~ v5_funct_1(B_144,A_59)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59)
      | r1_tarski(A_11,k1_relat_1(A_59))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_476])).

tff(c_492,plain,(
    ! [A_149,A_150,B_151] :
      ( ~ r2_hidden('#skF_2'(A_149,k1_relat_1(A_150)),k1_relat_1(B_151))
      | ~ v5_funct_1(B_151,A_150)
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151)
      | r1_tarski(A_149,k1_relat_1(A_150))
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_478])).

tff(c_508,plain,(
    ! [B_152,A_153] :
      ( ~ v5_funct_1(B_152,A_153)
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153)
      | r1_tarski(k1_relat_1(B_152),k1_relat_1(A_153)) ) ),
    inference(resolution,[status(thm)],[c_12,c_492])).

tff(c_32,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_538,plain,
    ( ~ v5_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_508,c_32])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_538])).

%------------------------------------------------------------------------------
