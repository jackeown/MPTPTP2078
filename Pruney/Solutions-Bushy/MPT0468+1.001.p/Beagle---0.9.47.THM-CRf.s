%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0468+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:21 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   40 (  56 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 (  91 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > o_1_1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(o_1_1_relat_1,type,(
    o_1_1_relat_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => m1_subset_1(o_1_1_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_1_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_19] :
      ( m1_subset_1(o_1_1_relat_1(A_19),A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    ! [A_39,B_40] :
      ( k4_tarski('#skF_2'(A_39,B_40),'#skF_3'(A_39,B_40)) = B_40
      | ~ r2_hidden(B_40,A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,B_36)
      | v1_xboole_0(B_36)
      | ~ m1_subset_1(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [B_25,C_26] : ~ r2_hidden(k4_tarski(B_25,C_26),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [B_25,C_26] :
      ( v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k4_tarski(B_25,C_26),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_16])).

tff(c_29,plain,(
    ! [B_25,C_26] : ~ m1_subset_1(k4_tarski(B_25,C_26),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_55,plain,(
    ! [B_43,A_44] :
      ( ~ m1_subset_1(B_43,'#skF_4')
      | ~ r2_hidden(B_43,A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_29])).

tff(c_80,plain,(
    ! [A_52,B_53] :
      ( ~ m1_subset_1(A_52,'#skF_4')
      | ~ v1_relat_1(B_53)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_83,plain,(
    ! [B_53] :
      ( ~ v1_relat_1(B_53)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(o_1_1_relat_1('#skF_4'),B_53)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_87,plain,(
    ! [B_54] :
      ( ~ v1_relat_1(B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(o_1_1_relat_1('#skF_4'),B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_83])).

tff(c_91,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_94,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_91])).

tff(c_12,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_94,c_12])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_97])).

tff(c_102,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_105,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_102,c_12])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_105])).

%------------------------------------------------------------------------------
