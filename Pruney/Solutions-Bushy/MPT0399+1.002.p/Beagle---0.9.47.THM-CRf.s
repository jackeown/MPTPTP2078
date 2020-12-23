%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0399+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:15 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 172 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :   71 ( 317 expanded)
%              Number of equality atoms :    8 (  25 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_37,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_13] : m1_subset_1('#skF_3'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_127,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_2'(A_50,B_51,C_52),B_51)
      | ~ r2_hidden(C_52,A_50)
      | ~ r1_setfam_1(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    ! [C_27,B_28,A_29] :
      ( ~ v1_xboole_0(C_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [C_30,A_31] :
      ( ~ v1_xboole_0(C_30)
      | ~ r2_hidden(A_31,'#skF_3'(k1_zfmisc_1(C_30))) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_59,plain,(
    ! [C_37,A_38] :
      ( ~ v1_xboole_0(C_37)
      | v1_xboole_0('#skF_3'(k1_zfmisc_1(C_37)))
      | ~ m1_subset_1(A_38,'#skF_3'(k1_zfmisc_1(C_37))) ) ),
    inference(resolution,[status(thm)],[c_14,c_46])).

tff(c_64,plain,(
    ! [C_39] :
      ( ~ v1_xboole_0(C_39)
      | v1_xboole_0('#skF_3'(k1_zfmisc_1(C_39))) ) ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_18,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    ! [C_43] :
      ( '#skF_3'(k1_zfmisc_1(C_43)) = k1_xboole_0
      | ~ v1_xboole_0(C_43) ) ),
    inference(resolution,[status(thm)],[c_64,c_18])).

tff(c_97,plain,(
    ! [C_44] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_44))
      | ~ v1_xboole_0(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_16,plain,(
    ! [C_19,B_18,A_17] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [A_17,C_44] :
      ( ~ r2_hidden(A_17,k1_xboole_0)
      | ~ v1_xboole_0(C_44) ) ),
    inference(resolution,[status(thm)],[c_97,c_16])).

tff(c_101,plain,(
    ! [C_44] : ~ v1_xboole_0(C_44) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_24])).

tff(c_30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_30])).

tff(c_112,plain,(
    ! [A_17] : ~ r2_hidden(A_17,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_138,plain,(
    ! [C_53,A_54] :
      ( ~ r2_hidden(C_53,A_54)
      | ~ r1_setfam_1(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_127,c_112])).

tff(c_151,plain,(
    ! [A_55,B_56] :
      ( ~ r1_setfam_1(A_55,k1_xboole_0)
      | r1_setfam_1(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_8,c_138])).

tff(c_163,plain,(
    ! [B_56] : r1_setfam_1('#skF_4',B_56) ),
    inference(resolution,[status(thm)],[c_22,c_151])).

tff(c_171,plain,(
    ! [B_58,A_59] :
      ( ~ r1_setfam_1(B_58,k1_xboole_0)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_181,plain,(
    ! [A_59] :
      ( v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_163,c_171])).

tff(c_186,plain,(
    ! [A_60] : ~ m1_subset_1(A_60,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_191,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_192,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_195,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_192,c_18])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_195])).

%------------------------------------------------------------------------------
