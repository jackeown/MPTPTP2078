%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0468+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:21 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  79 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_37,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_19] : m1_subset_1('#skF_4'(A_19),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31,plain,(
    ! [A_40,B_41] :
      ( k4_tarski('#skF_2'(A_40,B_41),'#skF_3'(A_40,B_41)) = B_41
      | ~ r2_hidden(B_41,A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_36,B_37] :
      ( r2_hidden(A_36,B_37)
      | v1_xboole_0(B_37)
      | ~ m1_subset_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [B_26,C_27] : ~ r2_hidden(k4_tarski(B_26,C_27),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [B_26,C_27] :
      ( v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k4_tarski(B_26,C_27),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_16])).

tff(c_29,plain,(
    ! [B_26,C_27] : ~ m1_subset_1(k4_tarski(B_26,C_27),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_55,plain,(
    ! [B_44,A_45] :
      ( ~ m1_subset_1(B_44,'#skF_5')
      | ~ r2_hidden(B_44,A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_29])).

tff(c_80,plain,(
    ! [A_53,B_54] :
      ( ~ m1_subset_1(A_53,'#skF_5')
      | ~ v1_relat_1(B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_85,plain,(
    ! [B_55] :
      ( ~ v1_relat_1(B_55)
      | v1_xboole_0(B_55)
      | ~ m1_subset_1('#skF_4'('#skF_5'),B_55) ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_89,plain,
    ( ~ v1_relat_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_85])).

tff(c_92,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_89])).

tff(c_12,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_92,c_12])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_95])).

tff(c_100,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_103,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_100,c_12])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_103])).

%------------------------------------------------------------------------------
