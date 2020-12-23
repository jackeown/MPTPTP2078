%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0845+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:57 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   43 (  55 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 102 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > #nlpp > o_1_0_mcart_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_0_mcart_1,type,(
    o_1_0_mcart_1: $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(o_1_0_mcart_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_mcart_1)).

tff(f_55,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(o_1_0_mcart_1(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [D_41,A_42,B_43] :
      ( ~ r2_hidden(D_41,'#skF_2'(A_42,B_43))
      | ~ r2_hidden(D_41,B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    ! [A_44,A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_44,'#skF_2'(A_45,B_46)),B_46)
      | ~ r2_hidden(A_45,B_46)
      | r1_xboole_0(A_44,'#skF_2'(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_95,plain,(
    ! [A_47,A_48] :
      ( ~ r2_hidden(A_47,A_48)
      | r1_xboole_0(A_48,'#skF_2'(A_47,A_48)) ) ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( r1_xboole_0(B_3,A_2)
      | ~ r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_49,A_50] :
      ( r1_xboole_0('#skF_2'(A_49,A_50),A_50)
      | ~ r2_hidden(A_49,A_50) ) ),
    inference(resolution,[status(thm)],[c_95,c_6])).

tff(c_45,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_2'(A_30,B_31),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [B_20] :
      ( ~ r1_xboole_0(B_20,'#skF_3')
      | ~ r2_hidden(B_20,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [A_30] :
      ( ~ r1_xboole_0('#skF_2'(A_30,'#skF_3'),'#skF_3')
      | ~ r2_hidden(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_45,c_22])).

tff(c_119,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_50])).

tff(c_136,plain,(
    ! [A_6] : r1_xboole_0(A_6,'#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_39,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ! [A_28] :
      ( ~ r1_xboole_0(A_28,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_39,c_22])).

tff(c_60,plain,(
    ! [A_28] :
      ( ~ r1_xboole_0(A_28,'#skF_3')
      | ~ m1_subset_1(A_28,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_162,plain,(
    ! [A_54] : ~ m1_subset_1(A_54,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_60])).

tff(c_167,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_168,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_168,c_16])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_172])).

%------------------------------------------------------------------------------
