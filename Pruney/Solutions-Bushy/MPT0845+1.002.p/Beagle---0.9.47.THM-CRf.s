%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0845+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:57 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
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
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_56,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    ! [D_42,A_43,B_44] :
      ( ~ r2_hidden(D_42,'#skF_3'(A_43,B_44))
      | ~ r2_hidden(D_42,B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_84,plain,(
    ! [A_45,A_46,B_47] :
      ( ~ r2_hidden('#skF_2'(A_45,'#skF_3'(A_46,B_47)),B_47)
      | ~ r2_hidden(A_46,B_47)
      | r1_xboole_0(A_45,'#skF_3'(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_95,plain,(
    ! [A_48,A_49] :
      ( ~ r2_hidden(A_48,A_49)
      | r1_xboole_0(A_49,'#skF_3'(A_48,A_49)) ) ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_50,A_51] :
      ( r1_xboole_0('#skF_3'(A_50,A_51),A_51)
      | ~ r2_hidden(A_50,A_51) ) ),
    inference(resolution,[status(thm)],[c_95,c_6])).

tff(c_45,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_3'(A_31,B_32),B_32)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [B_21] :
      ( ~ r1_xboole_0(B_21,'#skF_4')
      | ~ r2_hidden(B_21,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    ! [A_31] :
      ( ~ r1_xboole_0('#skF_3'(A_31,'#skF_4'),'#skF_4')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_45,c_22])).

tff(c_119,plain,(
    ! [A_52] : ~ r2_hidden(A_52,'#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_50])).

tff(c_136,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_39,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    ! [A_29] :
      ( ~ r1_xboole_0(A_29,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_29,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39,c_22])).

tff(c_60,plain,(
    ! [A_29] :
      ( ~ r1_xboole_0(A_29,'#skF_4')
      | ~ m1_subset_1(A_29,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_162,plain,(
    ! [A_55] : ~ m1_subset_1(A_55,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_60])).

tff(c_167,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_168,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_16,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_168,c_16])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_172])).

%------------------------------------------------------------------------------
