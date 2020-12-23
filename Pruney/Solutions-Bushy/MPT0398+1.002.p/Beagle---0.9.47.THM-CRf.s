%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0398+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:15 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 105 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_37,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_setfam_1)).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_13] : m1_subset_1('#skF_3'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,(
    ! [C_27,B_28,A_29] :
      ( ~ v1_xboole_0(C_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    ! [C_33,A_34] :
      ( ~ v1_xboole_0(C_33)
      | ~ r2_hidden(A_34,'#skF_3'(k1_zfmisc_1(C_33))) ) ),
    inference(resolution,[status(thm)],[c_12,c_39])).

tff(c_57,plain,(
    ! [C_37,A_38] :
      ( ~ v1_xboole_0(C_37)
      | v1_xboole_0('#skF_3'(k1_zfmisc_1(C_37)))
      | ~ m1_subset_1(A_38,'#skF_3'(k1_zfmisc_1(C_37))) ) ),
    inference(resolution,[status(thm)],[c_14,c_45])).

tff(c_62,plain,(
    ! [C_39] :
      ( ~ v1_xboole_0(C_39)
      | v1_xboole_0('#skF_3'(k1_zfmisc_1(C_39))) ) ),
    inference(resolution,[status(thm)],[c_12,c_57])).

tff(c_18,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_67,plain,(
    ! [C_40] :
      ( '#skF_3'(k1_zfmisc_1(C_40)) = k1_xboole_0
      | ~ v1_xboole_0(C_40) ) ),
    inference(resolution,[status(thm)],[c_62,c_18])).

tff(c_95,plain,(
    ! [C_44] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_44))
      | ~ v1_xboole_0(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_12])).

tff(c_16,plain,(
    ! [C_19,B_18,A_17] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_98,plain,(
    ! [A_17,C_44] :
      ( ~ r2_hidden(A_17,k1_xboole_0)
      | ~ v1_xboole_0(C_44) ) ),
    inference(resolution,[status(thm)],[c_95,c_16])).

tff(c_99,plain,(
    ! [C_44] : ~ v1_xboole_0(C_44) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_21])).

tff(c_26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_10])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_26])).

tff(c_111,plain,(
    ! [A_48] : ~ r2_hidden(A_48,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_127,plain,(
    ! [B_2] : r1_setfam_1(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_8,c_111])).

tff(c_20,plain,(
    ~ r1_setfam_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_20])).

%------------------------------------------------------------------------------
