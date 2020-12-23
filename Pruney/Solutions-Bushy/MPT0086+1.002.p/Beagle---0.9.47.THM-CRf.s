%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0086+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:42 EST 2020

% Result     : Theorem 26.41s
% Output     : CNFRefutation 26.45s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  49 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [D_38,A_39,B_40] :
      ( r2_hidden(D_38,A_39)
      | ~ r2_hidden(D_38,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_131,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_39,B_40)),A_39)
      | v1_xboole_0(k3_xboole_0(A_39,B_40)) ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_108,plain,(
    ! [D_35,B_36,A_37] :
      ( r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k3_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2142,plain,(
    ! [A_175,B_176] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_175,B_176)),B_176)
      | v1_xboole_0(k3_xboole_0(A_175,B_176)) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_28,plain,(
    ! [D_18,B_14,A_13] :
      ( ~ r2_hidden(D_18,B_14)
      | ~ r2_hidden(D_18,k4_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91092,plain,(
    ! [A_1255,A_1256,B_1257] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_1255,k4_xboole_0(A_1256,B_1257))),B_1257)
      | v1_xboole_0(k3_xboole_0(A_1255,k4_xboole_0(A_1256,B_1257))) ) ),
    inference(resolution,[status(thm)],[c_2142,c_28])).

tff(c_91469,plain,(
    ! [A_1258,A_1259] : v1_xboole_0(k3_xboole_0(A_1258,k4_xboole_0(A_1259,A_1258))) ),
    inference(resolution,[status(thm)],[c_131,c_91092])).

tff(c_48,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92012,plain,(
    ! [A_1258,A_1259] : k3_xboole_0(A_1258,k4_xboole_0(A_1259,A_1258)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91469,c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_92,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k3_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    k3_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_50])).

tff(c_101,plain,(
    k3_xboole_0('#skF_7',k4_xboole_0('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_92061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92012,c_101])).

%------------------------------------------------------------------------------
