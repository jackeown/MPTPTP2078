%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0760+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:49 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  56 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > o_2_0_wellord1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(o_2_0_wellord1,type,(
    o_2_0_wellord1: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => m1_subset_1(o_2_0_wellord1(A,B),k1_wellord1(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_0_wellord1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_30,plain,(
    k1_wellord1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(o_2_0_wellord1(A_13,B_14),k1_wellord1(B_14,A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [D_36,B_37,A_38] :
      ( r2_hidden(k4_tarski(D_36,B_37),A_38)
      | ~ r2_hidden(D_36,k1_wellord1(A_38,B_37))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_18,C_19,A_17] :
      ( r2_hidden(B_18,k3_relat_1(C_19))
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_87,plain,(
    ! [B_42,A_43,D_44] :
      ( r2_hidden(B_42,k3_relat_1(A_43))
      | ~ r2_hidden(D_44,k1_wellord1(A_43,B_42))
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_62,c_24])).

tff(c_123,plain,(
    ! [B_62,A_63,A_64] :
      ( r2_hidden(B_62,k3_relat_1(A_63))
      | ~ v1_relat_1(A_63)
      | v1_xboole_0(k1_wellord1(A_63,B_62))
      | ~ m1_subset_1(A_64,k1_wellord1(A_63,B_62)) ) ),
    inference(resolution,[status(thm)],[c_22,c_87])).

tff(c_127,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(A_65,k3_relat_1(B_66))
      | v1_xboole_0(k1_wellord1(B_66,A_65))
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_20,c_123])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_142,plain,
    ( v1_xboole_0(k1_wellord1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_32])).

tff(c_148,plain,(
    v1_xboole_0(k1_wellord1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_142])).

tff(c_28,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,(
    k1_wellord1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_148,c_28])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_151])).

%------------------------------------------------------------------------------
