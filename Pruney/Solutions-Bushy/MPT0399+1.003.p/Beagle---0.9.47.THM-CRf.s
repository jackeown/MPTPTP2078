%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0399+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:15 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 124 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 228 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_37,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_13] : m1_subset_1('#skF_3'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_23,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_27,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_23])).

tff(c_28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_10])).

tff(c_22,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_2'(A_36,B_37,C_38),B_37)
      | ~ r2_hidden(C_38,A_36)
      | ~ r1_setfam_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( ~ v1_xboole_0(B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [B_39,C_40,A_41] :
      ( ~ v1_xboole_0(B_39)
      | ~ r2_hidden(C_40,A_41)
      | ~ r1_setfam_1(A_41,B_39) ) ),
    inference(resolution,[status(thm)],[c_58,c_18])).

tff(c_84,plain,(
    ! [B_46,A_47,B_48] :
      ( ~ v1_xboole_0(B_46)
      | ~ r1_setfam_1(A_47,B_46)
      | r1_setfam_1(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_88,plain,(
    ! [B_48] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_setfam_1('#skF_4',B_48) ) ),
    inference(resolution,[status(thm)],[c_22,c_84])).

tff(c_92,plain,(
    ! [B_48] : r1_setfam_1('#skF_4',B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_88])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,(
    ! [B_50,B_51,A_52] :
      ( ~ v1_xboole_0(B_50)
      | ~ r1_setfam_1(B_51,B_50)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1(A_52,B_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_63])).

tff(c_104,plain,(
    ! [B_48,A_52] :
      ( ~ v1_xboole_0(B_48)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_52,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_99])).

tff(c_107,plain,(
    ! [A_53] : ~ m1_subset_1(A_53,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_112,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_113,plain,(
    ! [B_48] :
      ( ~ v1_xboole_0(B_48)
      | v1_xboole_0('#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_114,plain,(
    ! [B_48] : ~ v1_xboole_0(B_48) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_28])).

tff(c_119,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_16,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_119,c_16])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_122])).

%------------------------------------------------------------------------------
